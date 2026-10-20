/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Alternating
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completion from an extended alternating Cech complex

@stack 091V

For a finite family `f : Fin r → A`, this file owns the extended alternating Cech object in
`D(A)`, its projection to `A[0]`, and the resulting explicit internal-Hom completion functor and
unit.  The completeness and universal-property assertions are separated from those concrete data.

The closed structure and the identification of `A[0]` with the ambient tensor unit remain
explicit because neither is determined by an arbitrary monoidal structure on `D(A)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open LocalizedModule.Away.Cech.Alternating

universe u

namespace DerivedCategory.CechCompletion

variable {A : Type u} [CommRing A]

/-- The regular `A`-module placed in degree zero in `D(A)`. -/
@[stacks 091V "regular degree-zero derived module"]
abbrev regular : DerivedCategory (ModuleCat A) :=
  (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj (ModuleCat.of A A)

/-- The extended alternating Cech complex of a finite family, viewed in `D(A)`. -/
@[stacks 091V "extended alternating Cech derived object"]
abbrev source {r : ℕ} (f : Fin r → A) : DerivedCategory (ModuleCat A) :=
  (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
    DerivedCategory (ModuleCat A)).obj
    ((extended f A).extend embeddingUpNat)

/-- The projection from the extended alternating Cech complex to the regular module in degree
zero. -/
@[stacks 091V "extended alternating Cech projection"]
noncomputable def complexProjection {r : ℕ} (f : Fin r → A) :
    extended f A ⟶ (CochainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) :=
  (CochainComplex.toSingle₀Equiv (extended f A) (ModuleCat.of A A)).symm
    (𝟙 (ModuleCat.of A A))

/-- The projection from the extended alternating Cech object in `D(A)` to `A[0]`. -/
@[stacks 091V "extended alternating Cech derived projection"]
noncomputable def projection {r : ℕ} (f : Fin r → A) :
    source f ⟶ regular :=
  (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
    DerivedCategory (ModuleCat A)).map
      ((HomologicalComplex.extendMap (complexProjection f) embeddingUpNat) ≫
        (HomologicalComplex.extendSingleIso embeddingUpNat (ModuleCat.of A A)
          (0 : ℕ) (0 : ℤ) rfl).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A A)).symm.hom

section Closed

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]

/-- The explicit Cech completion functor `K ↦ RHom_A(Cech(f), K)`. -/
@[stacks 091V "Cech derived-completion functor"]
noncomputable abbrev functor {r : ℕ}
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : Fin r → A) :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A) :=
  MonoidalClosed.ihomOf H (source f)

/-- The explicit Cech completion object `RHom_A(Cech(f), K)`. -/
@[stacks 091V "Cech derived-completion object"]
noncomputable abbrev obj {r : ℕ}
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : Fin r → A) (K : DerivedCategory (ModuleCat A)) :
    DerivedCategory (ModuleCat A) :=
  (functor H f).obj K

/-- The functorial map from `K` to its explicit Cech completion, induced by the projection
`Cech(f) ⟶ A[0]` and an explicit identification of `A[0]` with the ambient tensor unit. -/
@[stacks 091V "Cech derived-completion unit"]
noncomputable def unit {r : ℕ}
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (s : regular ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (f : Fin r → A) :
    𝟭 (DerivedCategory (ModuleCat A)) ⟶ functor H f :=
  MonoidalClosed.unitOfPreOfIsoUnit H s (projection f)

/-- If `f` generates `I`, then the explicit Cech completion of every object is derived complete
with respect to `I`. -/
@[stacks 091V "Cech completion is derived complete"]
theorem obj_isDerivedComplete {r : ℕ} (I : Ideal A)
    (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (K : DerivedCategory (ModuleCat A)) :
    (obj H f K).IsDerivedCompleteWithRespectTo I := sorry

/-- Precomposition with the explicit Cech-completion unit is a bijection on morphisms into every
derived-complete object. -/
@[stacks 091V "Cech completion universal Hom bijection"]
theorem unit_bijective {r : ℕ} (I : Ideal A)
    (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (s : regular ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (K E : DerivedCategory (ModuleCat A))
    (hE : E.IsDerivedCompleteWithRespectTo I) :
    Function.Bijective
      (fun phi : obj H f K ⟶ E ↦ (unit H s f).app K ≫ phi) := sorry

end Closed

end DerivedCategory.CechCompletion
