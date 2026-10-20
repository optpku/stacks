module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
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
#check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_eq_top p x0 x0' φ :
  infinitesimalAutomorphismsAt p x0 x0' φ = (⊤ : Subgroup (Aut x0')))
#check (CategoryTheory.Functor.instUniqueIso_residueFiber p x0 x0 : Unique (Aut x0))

/- Remark 90.19.4 (2): for x0, y0 in Ob(F(k)) there is a unique isomorphism x0 ⟶ y0
and hence a canonical identification Inf_x0(F) = Inf_y0(F). -/
@[stacks 06JS]
#check (CategoryTheory.Functor.instUniqueIso_residueFiber p x0 y0 : Unique (x0 ≅ y0))
#check (CategoryTheory.Functor.infAutAtCanonicalIso p φ ψ :
  infinitesimalAutomorphismsAt p x0 x0' φ ≃* infinitesimalAutomorphismsAt p y0 y0' ψ)
#check (CategoryTheory.Functor.infAutAtCanonicalIso_apply p φ ψ :
  ∀ α : infinitesimalAutomorphismsAt p x0 x0' φ,
    (infAutAtCanonicalIso p φ ψ α).val =
      (fiberIso_of_fiberIso p (residueFiberIso p x0 y0) φ ψ).conjAut α.val)

/- Remark 90.19.4 (3): since F(k) is nonempty, choosing x0 in Ob(F(k)) and setting
Inf(F) = Inf_x0(F) yields a well-defined group of infinitesimal automorphisms of F. -/
@[stacks 06JS]
#check (CategoryTheory.Functor.infinitesimalAutomorphisms p : Type w)
#check (CategoryTheory.Functor.infinitesimalAutomorphismsEquivAt p x0 x0' φ :
  infinitesimalAutomorphisms p ≃* infinitesimalAutomorphismsAt p x0 x0' φ)
#check (CategoryTheory.Functor.infinitesimalAutomorphismsEquivAt_apply p x0 x0' φ :
  ∀ α : infinitesimalAutomorphisms p,
    (infinitesimalAutomorphismsEquivAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p (residueFiberIso p (chosenResidueFiberObj p) x0)
        (chosenDualNumberHom p (chosenResidueFiberObj p)) φ).conjAut α)

/- Remark 90.19.4 (4): with this notation Inf(F_x0) = Inf_x0(F). Compare with the
equality T F_x0 = T_x0 F in Remark 90.12.5. -/
@[stacks 06JS]
#check (CategoryTheory.Functor.infinitesimalAutomorphisms_sliceAt p x0 x0' φ :
  infinitesimalAutomorphisms (sliceAt p x0) ≃* infinitesimalAutomorphismsAt p x0 x0' φ)
#check (CategoryTheory.Functor.infinitesimalAutomorphisms_sliceAt_apply p x0 x0' φ :
  ∀ α : infinitesimalAutomorphisms (sliceAt p x0),
    (infinitesimalAutomorphisms_sliceAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p
        (residueFiberIso p
          (sliceFiberObj p x0 (chosenResidueFiberObj (sliceAt p x0))) x0)
        (sliceChosenDualNumberHom p x0 (chosenResidueFiberObj (sliceAt p x0))) φ).conjAut
        (sliceFiberAutMulEquiv p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k)
            (chosenResidueFiberObj (sliceAt p x0))) α))
