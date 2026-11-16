# TELL

`python tell_compare.py examples/compare.json` compares proposed rule models on a
finite set of ground queries. Expected statuses produce concrete counterexamples;
observed outcome classes suggest a distinguishing next query without counting
duplicate models as extra evidence. Program/dependency hashes and source-pin
checks are retained. Evaluation limits stay partial. Agreement covers supplied
queries; it does not establish program equivalence. Model generation remains
external, and programs with file dependencies are trusted local inputs.

Testimony, Experience and Language Logic. This standalone runtime evaluates anchored facts and rules, propagates premise tiers, performs exact arithmetic and records derivations. Its advanced commands analyze dependencies, test hypothetical changes and search for minimal input withdrawals.

    python tell.py run example.tell
    python tell.py query example.tell "capacity(X)" --why
    python -m unittest

The example derives capacity(6) from three synthetic units. Use --help on a command for options. Programs may reference local input files. Use programs and source paths you trust.


## Find sufficient assumptions

    python tell.py explain-gain gain.tell ready --candidate power --candidate signal --candidate override

The example returns two inclusion-minimal ways to derive ready. Override suffices by itself, or power and signal suffice together. The command evaluates hypothetical additions against one parsed snapshot, applies normal gates and defeaters, and returns the observation behind each result. An already-held goal has an empty sufficient set. Choose --width for the maximum number of simultaneous additions and --budget for the evaluation count. Consult complete_within_width before treating the list as exhaustive.

## Evaluation hardening

Comparison pins the bytes actually loaded for the main program and every include, plus declared anchor files. Changed or deleted inputs produce per-candidate `INPUT_CHANGED`, no observations, and no accepted result. `program_files`, `anchor_files` and `inputs_unchanged` record checked fingerprints. These are endpoint content checks on trusted local inputs, not file locks; a transient edit restored between checks may go undetected.

## Local-only distribution

Run the CLI or Python modules locally. No HTTP endpoint, hosting setup or provider
account is required. [Public distribution policy](PUBLIC_DISTRIBUTION.md).

`status_follow_up` uses the expected answers already supplied to identify the
next unanswered ground query. It considers complete models consistent with
those answers, groups identical remaining status predictions, and minimizes the
largest group of predictions that could survive one answer. Each branch lists
its models. Copies and tier-only differences cannot add votes. Incomplete
candidates are listed separately; the result is conditional on the supplied models.

Set `"status_objective": "expected_remaining"` in a comparison packet to choose
the query minimizing the expected number of remaining status classes. Each
distinct eligible prediction signature receives equal weight. For answer groups
of sizes 1 and 2, the expected remainder is (1² + 2²)/3 = 5/3. The report
includes the reduced fraction. The default objective remains `minimax`.

Set `"status_objective": "optimal_depth"` to minimize the worst-case number of
questions needed to identify one eligible prediction class. TELL searches the
finite decision tree using the supplied queries and caches repeated subsets.
After receiving an answer, set that query's expected status and run again.
`minimum_worst_case_questions` counts the selected question and all remaining
ones on the longest optimal branch. Equal-depth choices retain input order.
