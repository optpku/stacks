module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped ModuleCat.Algebra

universe u

namespace ModuleCat

/-- For commutative rings `A` and `B`, an equivalence between their module
categories is naturally isomorphic to extension of scalars along a ring
equivalence followed by tensoring with an invertible `B`-module. -/
theorem equivalence_tensor_invertible
    {A B : Type u} [CommRing A] [CommRing B]
    (F : ModuleCat A ⥤ ModuleCat B) [F.IsEquivalence] :
    ∃ (e : A ≃+* B) (L : ModuleCat B),
        Module.Invertible B L ∧
        Nonempty (F ≅
          ModuleCat.extendScalars e.toRingHom ⋙
            tensorRight L) := sorry

/-- For commutative rings `R`, `A`, and `B` with `R`-algebra structures, an
`R`-linear equivalence between the module categories of `A` and `B` is
naturally isomorphic to extension of scalars along an `R`-algebra equivalence
followed by tensoring with an invertible `B`-module. -/
theorem equivalence_tensor_invertible_linear
    {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    (F : ModuleCat A ⥤ ModuleCat B) [F.IsEquivalence] [F.Linear R] :
    ∃ (e : A ≃ₐ[R] B) (L : ModuleCat B),
      Module.Invertible B L ∧
        Nonempty (F ≅
          ModuleCat.extendScalars e.toRingHom ⋙
            tensorRight L) := sorry

end ModuleCat
