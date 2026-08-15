Port feature-complete terminal multiplexer to clean modern pure-function lean 4 using minimal code.

Instructions:
- High quality theorems are how we resolve tensions.
- Decouple "Session attach/detach/etc" and "TUI" like zmx.
- Isolate non-lean to smallest surface.
- We don't carry legacy decisions.
- The pieces run in userspace.
- When a machine reboots, the work resumes when we reopen, like tmux continuum/shutdown plugin.
- TUI: see windows from connected other machines over ssh when available.
- TUI: We don't need customization. We want modern clean default. Look at my tmux and zellij configs for the kind of interface I'm looking for.

Reference:
- https://github.com/tmux/tmux/ is the gold standard
- https://github.com/neurosnap/zmx and https://github.com/mdsakalu/zmx-session-manager are nicely decoupled
- https://github.com/martanne/abduco -- but unmaintained
- https://github.com/zellij-org/zellij -- Love the interface but seems to crash under high cpu or memory load. Need theorems preventing this.
- https://github.com/kenn-io/ghosthub
- https://github.com/herdrdev/herdr
- Experimental: ~/CodebaseQUENNV/2026/lean-dean and ~/CodebaseQUENNV/2026/pcae-lean for structural inspiration.
- Experimental: ~/pytmux for a python port of tmux
- Experimental: ~/lean-tmux/ for an attempt that started as a port of tmux but wanted to become zmx.
