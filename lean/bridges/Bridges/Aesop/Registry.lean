/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.Aesop.RuleSet
public import Bridges.Monoids
public import Bridges.QuiversDeMorgan

/-!
# The arch and deck registries as Aesop rules

The generator of the draft article `docs/bridges` joins a registry of *arches*, lemmas
`(property of PSh C) ↔ (condition on C)`, with a registry of *decks*, small categories `C`
whose presheaves are a familiar structure, then specialises the arch at the deck. This file
puts both registries into the Aesop rule set `Bridges`, as normalisation `simp` rules, so that
stages 1 and 2 of the pipeline (join, specialise) become one call to `aesop`:

* the arches: Boolean (`isBooleanTopos_presheaf_iff_isGroupoid`) and De Morgan
  (`isDeMorganTopos_presheaf_iff_rightOreCondition`);
* the deck readings of the arch conditions: on `SingleObj M` (right `M`-sets) and on the free
  category `Paths Q` of a quiver (quiver representations).

The rules rewrite in one direction only, from the topos to the category: the Morita transfer,
which needs the other direction, is tested separately in `Bridges.Aesop.Experiment`.
-/

public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory

attribute [aesop norm simp (rule_sets := [Bridges])]
  isBooleanTopos_presheaf_iff_isGroupoid
  isDeMorganTopos_presheaf_iff_rightOreCondition

attribute [aesop norm simp (rule_sets := [Bridges])]
  isGroupoid_singleObj_iff
  rightOreCondition_singleObj_iff
  isGroupoid_paths_iff
  rightOreCondition_paths_iff

end LeanPool.ToposTheoreticBridges.Examples
