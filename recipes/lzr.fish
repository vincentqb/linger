# Import tmux-resurrect pane records as independent linger sessions.
# Windows, layouts, active state, groups, and captured contents are ignored.
function lzr --description 'import tmux-resurrect panes as linger sessions'
    set -l restore_processes false
    if test (count $argv) -gt 0; and test "$argv[1]" = --restore-processes
        set restore_processes true
        set -e argv[1]
    end
    if test (count $argv) -gt 1
        printf 'usage: lzr [--restore-processes] [SAVE]\n' >&2
        return 2
    end

    set -l save
    if test (count $argv) -eq 1
        set save "$argv[1]"
    else if test -d "$HOME/.tmux/resurrect"
        set save "$HOME/.tmux/resurrect/last"
    else
        set -l data_home "$HOME/.local/share"
        if set -q XDG_DATA_HOME; and test -n "$XDG_DATA_HOME"
            set data_home "$XDG_DATA_HOME"
        end
        set save "$data_home/tmux/resurrect/last"
    end
    if not test -f "$save"
        printf 'lzr: save not found: %s\n' "$save" >&2
        return 1
    end
    if not command -q linger
        printf 'lzr: linger is not on PATH\n' >&2
        return 1
    end

    set -l names
    set -l dirs
    set -l commands
    set -l tab (printf '\t')
    set -l line_number 0
    while read -l line
        set line_number (math $line_number + 1)
        set -l fields (string split "$tab" -- "$line")
        test "$fields[1]" = pane; or continue
        if test (count $fields) -ne 11
            printf 'lzr: malformed pane record at line %s\n' "$line_number" >&2
            return 1
        end
        if test -z "$fields[2]"; or test -z "$fields[3]"; or test -z "$fields[6]"
            printf 'lzr: malformed pane record at line %s\n' "$line_number" >&2
            return 1
        end
        if not string match -q ':*' -- "$fields[8]"; or not string match -q ':*' -- "$fields[11]"
            printf 'lzr: malformed pane record at line %s\n' "$line_number" >&2
            return 1
        end

        set -l dir (string sub -s 2 -- "$fields[8]")
        set dir (string replace -a "\\ " ' ' -- "$dir")
        if test "$dir" = '~'
            set dir "$HOME"
        else if string match -q '~/*' -- "$dir"
            set dir "$HOME"(string sub -s 2 -- "$dir")
        end
        if not test -d "$dir"
            printf 'lzr: working directory not found at line %s: %s\n' "$line_number" "$dir" >&2
            return 1
        end
        if not pushd "$dir" >/dev/null 2>/dev/null
            printf 'lzr: working directory not accessible at line %s: %s\n' "$line_number" "$dir" >&2
            return 1
        end
        popd >/dev/null

        set -l name (string join '' -- "$fields[2]" -w "$fields[3]" -p "$fields[6]")
        if test (string length -- "$name") -gt 80; or not string match -rq '^[A-Za-z0-9_+-][A-Za-z0-9_.+-]*$' -- "$name"
            printf 'lzr: projected session is not a valid linger name at line %s: %s\n' "$line_number" "$name" >&2
            return 1
        end
        if contains -- "$name" $names
            printf 'lzr: duplicate projected session: %s\n' "$name" >&2
            return 1
        end
        set -a names "$name"
        set -a dirs "$dir"
        set -a commands (string sub -s 2 -- "$fields[11]")
    end < "$save"

    if test (count $names) -eq 0
        printf 'lzr: no pane records in save: %s\n' "$save" >&2
        return 1
    end

    # Snapshot every local identity, including checkpoints with no daemon. A
    # failed listing is ambiguous, so fail closed rather than replay a command.
    # This is sequential only: run is an upsert, not an atomic create claim.
    set -l existing
    set -l listing (command linger ls --porcelain)
    if test $status -ne 0
        printf 'lzr: could not list existing linger sessions\n' >&2
        return 1
    end
    for line in $listing
        set -l fields (string split "$tab" -- "$line")
        if test (count $fields) -eq 2; and test "$fields[1]" = name
            set -a existing "$fields[2]"
        end
    end

    # A short fixed process set. Saved commands are still opt-in: without
    # --restore-processes, none are sent to a shell.
    set -l allowed vi vim view nvim emacs man less more tail top htop irssi weechat mutt
    set -l i 0
    for name in $names
        set i (math $i + 1)
        if contains -- "$name" $existing
            continue
        end

        if not pushd "$dirs[$i]" >/dev/null 2>/dev/null
            printf 'lzr: working directory became inaccessible: %s\n' "$dirs[$i]" >&2
            return 1
        end
        command linger run "$name" true
        set -l create_status $status
        popd >/dev/null
        if test $create_status -ne 0
            printf 'lzr: could not create session: %s\n' "$name" >&2
            return 1
        end

        if test "$restore_processes" = true; and test -n "$commands[$i]"
            set -l words (string split -n ' ' -- "$commands[$i]")
            if test (count $words) -gt 0; and contains -- "$words[1]" $allowed
                command linger run "$name" "$commands[$i]"
                if test $status -ne 0
                    printf 'lzr: could not restore process in session: %s\n' "$name" >&2
                    return 1
                end
            end
        end
    end
end
