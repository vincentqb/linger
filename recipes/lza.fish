# Attach that auto-reconnects while a link flaps (autossh style).
# ssh reserves exit 255 for its own failures, so only transport death
# retries; detach (ctrl-\) and normal session end exit non-255 and
# stop the loop. Known blind spot, inherent to ssh's exit contract: a
# remote shell that itself exits 255 is indistinguishable from a
# transport error and would respawn.
# Using mosh? You don't need this — mosh IS the reconnect layer:
#     mosh HOST -- linger attach NAME
function lza --description 'attach, reconnecting while the link flaps'
    while true
        linger attach $argv[1]              # name@host
        test $status -eq 255; or break    # 255 = ssh transport error
        sleep 2
    end
end
