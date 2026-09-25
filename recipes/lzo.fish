# Every session on HOST as a kitty tab, one shot — live AND resumable,
# so it recreates the whole workspace after a reboot of either machine
# (laptop rebooted: the daemons never died; host rebooted: attach
# restores each session from its checkpoint).
# Needs `allow_remote_control yes` in kitty.conf.
function lzo --description 'open every session on HOST as a kitty tab'
    if test (count $argv) -ne 1; or test -z "$argv[1]"
        printf 'usage: lzo HOST\n' >&2
        return 2
    end
    set -l host $argv[1]
    set -l listing (ssh -o BatchMode=yes -o ConnectTimeout=3 -- "$host" linger ls --porcelain)
    or return $status
    set -l names
    for line in $listing
        set -l fields (string split \t -- "$line")
        test "$fields[1]" = name; or continue
        if test (count $fields) -ne 2; or \
                not string match -rq '^[A-Za-z0-9_+-][A-Za-z0-9_.+-]{0,79}$' -- "$fields[2]"; or \
                contains -- "$fields[2]" $names
            printf 'lzo: invalid or duplicate session name in listing\n' >&2
            return 1
        end
        set -a names "$fields[2]"
    end
    for name in $names
        # roaming variant: replace the ssh line with
        #     mosh $host -- linger attach $name
        kitten @ launch --type=tab --tab-title "$name@$host" -- \
            ssh -t -- "$host" linger attach "$name"
        or return $status
    end
    return 0
end
