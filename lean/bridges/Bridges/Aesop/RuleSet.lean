/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Aesop

/-!
# The Aesop rule set of the arch registry

An Aesop rule set must be declared in a module that its users import, so the declaration of
`Bridges` has a file of its own. The rules are added in `Bridges.Aesop.Registry`, and the
experiment that uses them is `Bridges.Aesop.Experiment`.
-/

declare_aesop_rule_sets [Bridges]
