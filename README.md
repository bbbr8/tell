# TELL

Testimony, Experience and Language Logic. This standalone runtime evaluates anchored facts and rules, propagates premise tiers, performs exact arithmetic and records derivations. Its advanced commands analyze dependencies, test hypothetical changes and search for minimal input withdrawals.

    python tell.py run example.tell
    python tell.py query example.tell "capacity(X)" --why
    python -m unittest

The example derives capacity(6) from three synthetic units. Use --help on a command for options. Programs may reference local input files. Use programs and source paths you trust.


## Find sufficient assumptions

    python tell.py explain-gain gain.tell ready --candidate power --candidate signal --candidate override

The example returns two inclusion-minimal ways to derive ready. Override suffices by itself, or power and signal suffice together. The command evaluates hypothetical additions against one parsed snapshot, applies normal gates and defeaters, and returns the observation behind each result. An already-held goal has an empty sufficient set. Choose --width for the maximum number of simultaneous additions and --budget for the evaluation count. Consult complete_within_width before treating the list as exhaustive.
