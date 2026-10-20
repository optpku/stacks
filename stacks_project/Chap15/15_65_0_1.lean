/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Exact
public import ReasLib.Algebra.Module.FiniteFreeResolution
import StacksCheckRecall

/-!
# 15.65.0.1

@stack 064P
-/

@[expose] public section

universe u v

/-
Domain-style sampling for finite free resolutions of modules:
- primary domain: recursive finite free resolutions in module theory
- same-domain declarations inspected:
  `Module.Finite.iff_exists_surjective_free`,
  `Module.HasLengthFiniteFreeResolution`,
  `Module.hasLengthFiniteFreeResolution_succ_iff`,
  `HasFiniteFreeResolutionLengthLE`

Layer triage:
- `source-facing`: the recursive exact-length finite free resolution notion from item `15.65.0.1`
- `core/canonical`: the ReasLib owner `Module.HasLengthFiniteFreeResolution`, together with the
  finite-generation owner `Module.Finite`
- `bridge/view`: Chapter 10's bounded-complex formulation `HasFiniteFreeResolutionLengthLE`

Primitive data is finite generation of `M`, equivalently a surjection `R^n → M`, and the recursive
length predicate is built by iterating kernels of finite free covers in the module universe of `M`.
The successor unpacking statement is derived API. Since the exact source-facing owner already
exists canonically in ReasLib, this file should reuse it directly rather than keep a parallel
local wrapper with duplicate names.
-/

section

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- 15.65.0.1: the length-`0` case is finite generation of `M`, equivalently a surjection from a
standard finite free module `R^n` onto `M`. -/
#check Module.Finite.iff_exists_surjective_free

/- 15.65.0.1: the recursive notion that `M` admits a length-`n` finite free resolution is the
canonical ReasLib owner `Module.HasLengthFiniteFreeResolution R M`. -/
@[stacks 064P "finite free resolution of prescribed length"]
#check Module.HasLengthFiniteFreeResolution R M

/- The successor step is the canonical unpacking theorem: resolving `M` for `n + 1` steps is the
same as choosing one finite free cover of `M` and resolving its kernel for `n` further steps. -/
#check Module.hasLengthFiniteFreeResolution_succ_iff

end
