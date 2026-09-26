#!/bin/sh
# Open live and resumable sessions on HOST as kitty tabs.
# Requires allow_remote_control yes in kitty.conf.
if [ "$#" -ne 1 ] || [ -z "$1" ]; then
    printf 'usage: lzo HOST\n' >&2
    exit 2
fi
host=$1
listing=$(ssh -o BatchMode=yes -o ConnectTimeout=3 -- "$host" linger ls --porcelain) || exit "$?"
# Validate every name before the first launch; a failed awk cannot leak its prefix.
names=$(printf '%s\n' "$listing" | LC_ALL=C awk -F '\t' '
    $1 == "name" {
        if (NF != 2 || length($2) > 80 ||
            $2 !~ /^[A-Za-z0-9_+-][A-Za-z0-9_.+-]*$/ || seen[$2]++) exit 1
        print $2
    }
') || {
    printf 'lzo: invalid or duplicate session name in listing\n' >&2
    exit 1
}
[ -n "$names" ] || exit 0
while IFS= read -r name; do
    kitten @ launch --type=tab --tab-title "$name@$host" -- \
        ssh -t -- "$host" linger attach "$name" || exit "$?"
done <<LZO_NAMES
$names
LZO_NAMES
exit 0
