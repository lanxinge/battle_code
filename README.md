# 论战验证器

Lean 4 prototype for an auditable debate-rule verification framework.

## Layout

- Internal stable library: `VerseFramework`

Chinese-facing names are now defined directly inside the `VerseFramework` source modules rather than through a separate facade layer.

Current internal module split:

- `VerseFramework.Core`: abstract domain objects, family/world IDs, argument profiles, claims, destruction hierarchy, proof status.
- `VerseFramework.Core.Theory`: model-theory layer for the five-tuple `(M, g, Phi, B, C)` and the four core monadic-universe conditions.
- `VerseFramework.Core.Transfinite`: countable-tier target objects and ordinal-style tier labels for `omega*n`, `omega^n`, `omega^omega`, and fixed-point layers.
- `VerseFramework.Evidence`: atomic text evidence for worlds, pairs, families, and attacks.
- `VerseFramework.Assumptions`: explicit, named assumption packs only.
- `VerseFramework.Rules.Context`: evidence access and audit-trail helpers.
- `VerseFramework.Rules.Bridge.Monadic`: evidence-to-support bridge rules for monadic-world candidates.
- `VerseFramework.Rules.Judgement.Monadic`: strict monadic-universe judgements and argument-profile scale gates.
- `VerseFramework.Rules.Monadic`: compatibility facade importing the bridge/judgement split.
- `VerseFramework.Rules.Multiverse`: family-level rules, witness-pair multiverse rules, stronger whole-family strict multiverse rules, and argument-level multiverse support.
- `VerseFramework.Rules.Universe`: context-to-model bridge connecting auditable world judgements to the five-tuple model layer.
- `VerseFramework.Rules.Transfinite`: conservative rules for countable ordinal-style aggregation tiers above multiverse.
- `VerseFramework.Audit.Monadic`: auditable breakdown of connectedness, spacetime, dynamics, whole-world support, and argument-profile scale checks.
- `VerseFramework.Audit.Multiverse`: auditable pair/family checks with separate argument-level and strict statuses.
- `VerseFramework.Audit.Transfinite`: auditable checks for aggregate-totality, generation rules, and fixed-point closure requirements.
- `VerseFramework.Audit.Layers`: explicit premise-layer summaries tracking whether a conclusion used direct text facts, bridge rules, default assumptions, structural witnesses, blockers, or missing premises.

## Conservative Transfinite Policy

- Tiers above `omega` are not inferred from loose size language, continuum language, or automatic expansion of lower-tier members.
- Higher tiers only become provable when the user supplies explicit aggregate-level atoms stating that the generated hierarchy is treated as one total object, together with the required generation and closure facts.
- Assumption packs do not manufacture transfinite tiers; if the text does not explicitly commit to the aggregate object, the checker should stay negative or underdetermined.

## Premise Stratification

- `TextEvidence` stores only manually entered textual facts.
- Bridge rules are explicit named constructors in `VerseFramework.Core.Bridge`.
- Default charity lives only in named `AssumptionPack`s.
- `VerseFramework.Audit.Layers` computes a `LayerSummary` for each audit so you can ask whether a conclusion depended on direct text only, used bridge rules, or relied on default assumptions.
