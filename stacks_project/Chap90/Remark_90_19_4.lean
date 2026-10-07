module

public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
import StacksCheckRecall

/-!
# Infinitesimal automorphisms of a predeformation category

If `p` is a predeformation category, residue-fibre automorphism groups are trivial,
so `Inf_x0(F)` is the full dual-number automorphism group and is independent of the
chosen residue-fibre object. The resulting group `Inf(F)` identifies with
`Inf_x0(F)` after slicing, analogously to `T F_x0 = T_x0 F` in Remark 90.12.5.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
variable (x0 y0 : p.Fiber (residue Λ k))
variable (x0' y0' : p.Fiber (dualNumber Λ k))
variable (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
variable (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
variable [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
variable [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]

/- Remark 90.19.4 (1): for x0 in Ob(F(k)) the automorphism group Aut_k(x0) is trivial
and hence Inf_x0(F) = Aut_{k[ε]}(x'_0). -/
@[stacks 06JS]
#check (Functor.instUniqueAut_residueFiber p x0 : Unique (Aut x0))
@[stacks 06JS]
#check Functor.infinitesimalAutomorphismsAt_eq_top p x0 x0' φ

/- Remark 90.19.4 (2): for x0, y0 in Ob(F(k)) there is a unique isomorphism x0 ⟶ y0
and hence a canonical identification Inf_x0(F) = Inf_y0(F). -/
@[stacks 06JS]
#check Functor.infAutAtCanonicalIso p φ ψ

/- Remark 90.19.4 (3): since F(k) is nonempty, choosing x0 in Ob(F(k)) and setting
Inf(F) = Inf_x0(F) yields a well-defined group of infinitesimal automorphisms of F. -/
@[stacks 06JS]
#check Functor.infinitesimalAutomorphisms p
@[stacks 06JS]
#check Functor.infinitesimalAutomorphismsEquivAt p x0 x0' φ

/- Remark 90.19.4 (4): with this notation Inf(F_x0) = Inf_x0(F). Compare with the
equality T F_x0 = T_x0 F in Remark 90.12.5. -/
@[stacks 06JS]
#check Functor.infinitesimalAutomorphisms_sliceAt p x0 x0' φ
