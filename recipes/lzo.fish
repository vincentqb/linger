# Every session on HOST as a kitty tab, one shot — live AND resumable,
# so it recreates the whole workspace after a reboot of either machine
# (laptop rebooted: the daemons never died; host rebooted: attach
# restores each session from its checkpoint).
# Needs `allow_remote_control yes` in kitty.conf.
function lzo --description 'open every session on HOST as a kitty tab'
    set -l host $argv[1]
    for name in (ssh -o BatchMode=yes -o ConnectTimeout=3 -- $host \
                     linger ls --porcelain | awk -F '\t' '$1=="name"{print $2}')
        # roaming variant: replace the ssh line with
        #     mosh $host -- linger attach $name
        kitten @ launch --type=tab --tab-title "$name@$host" -- \
            ssh -t -- $host linger attach $name
    end
end
