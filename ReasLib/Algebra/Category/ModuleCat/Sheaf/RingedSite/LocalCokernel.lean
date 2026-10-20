module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Local
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cover-local cokernel properties of module sheaves

The root owner is an `ObjectProperty`, obtained by cover-localizing Mathlib's cokernel property.
The quasi-coherent form used in Chapter 17 is only one specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}

/-- Module sheaves which locally are cokernels of morphisms from `P`-objects to `Q`-objects. -/
def localCokernels
    (P Q : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U))) :
    ObjectProperty (SheafOfModules.{w} R) :=
  locally fun U ↦
    (MorphismProperty.ofObjectProperty (P U) (Q U)).cokernels

/-- The cover-and-cokernel criterion for membership in `localCokernels P Q`. -/
theorem localCokernels_iff
    (P Q : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U)))
    (M : SheafOfModules.{w} R) :
    localCokernels P Q M ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I,
          (MorphismProperty.ofObjectProperty (P (U i)) (Q (U i))).cokernels
            (M.over (U i)) := sorry

/-- The local-cokernel construction is monotone in both endpoint properties. -/
theorem localCokernels_mono
    {P P' Q Q' : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U))}
    (hP : ∀ U : C, P U ≤ P' U) (hQ : ∀ U : C, Q U ≤ Q' U) :
    localCokernels P Q ≤ localCokernels P' Q' := sorry

/-- A local-cokernel property is invariant under isomorphism. -/
instance localCokernels_isClosedUnderIsomorphisms
    (P Q : (U : C) → ObjectProperty (SheafOfModules.{w} (R.over U))) :
    (localCokernels P Q).IsClosedUnderIsomorphisms := sorry

namespace localCokernels

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Module sheaves which locally are cokernels of morphisms between quasi-coherent module
sheaves. -/
@[stacks 01C3 "local cokernel property"]
abbrev quasicoherent : ObjectProperty (SheafOfModules.{w} R) :=
  localCokernels
    (fun U ↦ SheafOfModules.isQuasicoherent (R.over U))
    (fun U ↦ SheafOfModules.isQuasicoherent (R.over U))

/-- The source-facing cover criterion for the quasi-coherent local-cokernel property. -/
theorem quasicoherent_iff (M : SheafOfModules.{w} R) :
    quasicoherent M ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I,
          (MorphismProperty.ofObjectProperty
            (SheafOfModules.isQuasicoherent (R.over (U i)))
            (SheafOfModules.isQuasicoherent (R.over (U i)))).cokernels
              (M.over (U i)) := sorry

/-- A quasi-coherent cokernel presentation on every member of one cover gives membership in
`localCokernels.quasicoherent`. -/
theorem quasicoherent_of_cover
    (M : SheafOfModules.{w} R) {I : Type u} (U : I → C)
    (hU : J.CoversTop U)
    (hM : ∀ i : I,
      (MorphismProperty.ofObjectProperty
        (SheafOfModules.isQuasicoherent (R.over (U i)))
        (SheafOfModules.isQuasicoherent (R.over (U i)))).cokernels
          (M.over (U i))) :
    quasicoherent M := sorry

end localCokernels

end SheafOfModules.RingedSite
