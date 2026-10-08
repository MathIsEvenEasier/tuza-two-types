Tuza's inequality for two neighborhood types
============================================

Every finite simple split graph with at most two distinct active
independent-side neighborhood types satisfies
``tau_triangle(G) <= 2 * nu_triangle(G)``.
The clique size, the overlap between neighborhoods, and their multiplicities
are unrestricted. Tuza's conjecture for arbitrary graphs remains open.

`Explore the proof <https://mathiseveneasier.github.io/tuza-two-types/>`_ ·
`Final Lean theorem <formal/Result.lean>`_ ·
`Complete certificate sources <https://github.com/MathIsEvenEasier/tuza-two-types/releases/tag/v1.0.0>`_

Statement
---------

Fix a partition of the vertices into a clique K and an independent set I.
For x in I, its type is its neighborhood in K. A type is active if it has
at least two vertices. There may be arbitrarily many vertices of either
active type, and arbitrarily many inactive vertices of any type.

A triangle packing consists of pairwise edge-disjoint triangles; its maximum
size is ``nu_triangle``. A triangle edge cover is a set of edges meeting every
triangle; its minimum size is ``tau_triangle``. Both optima are attained for finite graphs.

The endpoint is ``TuzaTwoTypes.tuza_of_two_active_types``. Its hypotheses
state precisely the partition and the bound on active types. All certificate comparisons are proved in the project and used to derive
this theorem.

Proof route
-----------

1. Remove inactive vertices. For a neighborhood of size s, recoloring
   preserves every triangle packing using at most h(s) twins, where
   h(s)=s-1 for even s and h(s)=s for odd s. A cover argument shows that
   the same cap preserves both optimization values.
2. Construct packing lower bounds with proper matching colors, compatible
   choices for the two overlapping neighborhoods, greedy core completion
   using Mantel's bound, and a sum-coloring argument.
3. Construct cover upper bounds from cuts, including shadow cuts and an
   unbalanced cut through the common neighborhood. These constructions
   give upper and lower bounds on the two optima.
4. Compare these bounds. Clique sizes 2 through 42 use a finite certificate
   covering 23,848,371 compressed parameter tuples. Analytic reductions and
   a closed interval certificate cover every size at least 43 at once.
   The interval certificate has 178,506 leaves. The cases below 2 have no triangles.
5. Proved assembly lemmas connect the numerical certificates back to every
   finite graph in the statement.

The continuous certificate is a proof on a real domain, with exact directed
integer rounding, certified splitting and exhaustive domain coverage.
Normalization includes 1/k, so all k >= 43 lie in a bounded domain covered
by the certificate.

What is verified
----------------

The complete theorem was checked in Lean 4.34.0 on 8 October 2026, with Mathlib
pinned to ``5ed2965256430c3649e86755f9576b54eca72435``.
The finished verification assembled hash-matched modules from bounded
Azure runs. The final dependency list is exactly ``propext``,
``Classical.choice``, and ``Quot.sound``. There are no project axioms,
proof holes, unsafe declarations, or native decision shortcuts.
The generated arithmetic proofs use ``decide +kernel``.
An intentionally false arithmetic proof was rejected.

`Verification summary <evidence/formalization-report.json>`_ and
`the exact theorem and axiom log <evidence/Result-compile.log>`_ preserve
this evidence. The original manifests retain the source and object hashes
and provenance of every accepted certificate module. Source hashes in the
release manifest match these previously checked files exactly.

The public source-build workflow rebuilds all 3,190 project modules without
accepting any compiled project objects as input. Its run status is available
under `Actions <https://github.com/MathIsEvenEasier/tuza-two-types/actions/workflows/lean.yml>`_.
Each run records how many modules compiled and whether the final theorem
and negative control passed.

Repository guide
----------------

* ``formal/GraphReductions.lean``: actual graph constructions, both optima,
  compression, scalar bounds, and the finite checker's soundness.
* ``formal/CertificateKernel.lean``: interval arithmetic, rounding,
  leaf soundness, contraction, splitting and domain coverage.
* ``formal/NormalizedBounds.lean``: graph-to-expression identities and
  the complete classification into the two certificate domains.
* ``formal/Result.lean``: the unconditional final graph theorem.
* ``certificates/source-manifest.json``: every source hash and both release assets.
* ``evidence/``: historical compilation records, final audit and cleanup receipts.
* ``scripts/`` and ``ci/``: source retrieval and a fresh build on a disposable Azure runner.
* ``docs/``: self-contained interactive proof guide, served by GitHub Pages.
* ``research-note.tex``: detailed development notes. The opening status and
  final formal-verification section describe the completed proof; intermediate
  sections also preserve earlier routes and historical checkpoints.

Reproduce
---------

Source retrieval and checksum verification are lightweight and may run locally::

    python3 scripts/sources.py /tmp/tuza-sources

This downloads about 10 MB and expands roughly 268 MB of Lean source. The
four main files are in Git; all 3,186 generated certificate modules are in
the two versioned release assets. No compiled Lean objects are distributed
as necessary build inputs. A changed, missing or extra source is rejected.

The supplied build workflow runs on Azure. The ``ci/azure/audit.py``
controller provisions a repository-scoped ephemeral runner, installs an
independent cloud deletion guard before compute starts, limits the worker
to 48 GiB without swap and 175 minutes, and sets a 185-minute cloud deadline.
It requires Azure CLI, GitHub CLI authorized for this repository, and
``AZURE_SUBSCRIPTION_ID``. From a control machine::

    python3 ci/azure/audit.py prepare
    python3 ci/azure/audit.py launch ci/azure/runs/JOB_ID
    gh workflow run lean.yml -f runner_label=azure-proof-JOB_ID

Use the actual job ID returned by ``prepare``. The workflow is restricted
to main. After the workflow completes, download its artifact and then run::

    gh run download RUN_ID --dir public-build-evidence
    python3 ci/azure/audit.py collect ci/azure/runs/JOB_ID

Check both the public workflow conclusion and ``rebuild-report.json``;
transport success alone does not establish proof success. ``collect``
retrieves transport records and confirms deletion of both resource groups.
If interrupted, use the saved job directory with ``status`` and ``collect``
(or ``cleanup`` after preserving diagnostics). The cloud guard does not depend
on the control machine staying awake. Do not commit registration tokens or
anything from ``ci/azure/runs``. The build refuses a local full compilation.

Context and references
----------------------

Zijian Zeng's 2026 preprint proves the two-type case for a specified
**eight-vertex** clique part, with arbitrary multiplicities. The statement
here removes the bound on the clique size. Bonamy and coauthors prove the
threshold-graph case, which includes nested neighborhoods. Publication priority has not been established, and the proof has not yet
received independent expert review.

* M. Bonamy, Ł. Bożyk, A. Grzesik, M. Hatzel, T. Masařík, J. Novotná,
  K. Okrasa, *Tuza's Conjecture for Threshold Graphs*, DMTCS 24(1), 2022:
  https://arxiv.org/abs/2105.09871
* Z. Zeng, *Tuza's Conjecture for Split Graphs with an Eight-Vertex Clique
  Part and Two Neighborhood Types*, preprint, 19 August 2026:
  https://www.preprints.org/manuscript/202608.1304
* L. Chahua and J. Gutiérrez, *On Tuza's conjecture in dense graphs*,
  Discrete Applied Mathematics 377 (2025), 225–233:
  https://arxiv.org/abs/2405.11409
* Mathlib contributors, the pinned implementation of Turán's theorem:
  https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
Research inspired by @xamualexander, Dr. Samuel Allen Alexander. Still there.
