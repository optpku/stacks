module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Basic
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Hom
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Morphisms of formal objects

Compatible stage maps determine morphisms of formal objects. Their maps on
complete local bases are reconstructed from the induced maps on all quotients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- A morphism of formal objects is a natural transformation of their stage functors. -/
abbrev Hom (ξ η : FormalObject X) : Type u := ξ.toFunctor ⟶ η.toFunctor

/-- Construct a morphism from stage maps commuting with successor transitions. -/
def Hom.ofStages {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) : Hom ξ η :=
  NatTrans.ofSequence app (by
    intro n
    dsimp only [toFunctor, Functor.ofSequence]
    rw [Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ]
    exact naturality n)

/-- The map of truncated spectra over the base scheme induced by a stage map. -/
def Hom.stageOverMap {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    ξ.base.stageOver n ⟶ η.base.stageOver n :=
  eqToHom (ξ.over_obj n).symm ≫ X.p.map (a.app n) ≫ eqToHom (η.over_obj n)

/-- The quotient ring homomorphism dual to the map of truncated spectra. -/
def Hom.quotientHom {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    η.base.truncationRing n →+* ξ.base.truncationRing n :=
  CommRingCat.Hom.hom <|
    (Scheme.ΓSpecIso (η.base.truncationRing n)).inv ≫ (a.stageOverMap n).left.appTop ≫
      (Scheme.ΓSpecIso (ξ.base.truncationRing n)).hom

/-- The induced quotient homomorphisms commute with successive quotient projections. -/
theorem Hom.quotientHom_naturality {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    (Ideal.Quotient.factorPow (maximalIdeal ξ.base.carrier) (Nat.le_succ (n + 1))).comp
        (a.quotientHom (n + 1)) =
      (a.quotientHom n).comp
        (Ideal.Quotient.factorPow (maximalIdeal η.base.carrier) (Nat.le_succ (n + 1))) :=
  sorry

/-- The ring homomorphism on complete local bases reconstructed from the stage maps. -/
def Hom.baseRingHom {ξ η : FormalObject X} (a : Hom ξ η) :
    η.base.carrier →+* ξ.base.carrier :=
  let completionQuotientHom :
      (n : ℕ) → η.base.carrier →+* ξ.base.carrier ⧸ maximalIdeal ξ.base.carrier ^ n
    | 0 =>
      { toFun := fun _ ↦ 0
        map_zero' := rfl
        map_one' := by
          symm
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          simp
        map_add' := fun _ _ ↦ (zero_add 0).symm
        map_mul' := fun _ _ ↦ (zero_mul 0).symm }
    | n + 1 => (a.quotientHom n).comp
        (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 1)))
  (AdicCompletion.ofAlgEquiv (maximalIdeal ξ.base.carrier)).symm.toRingHom.comp
    (AdicCompletion.liftRingHom (maximalIdeal ξ.base.carrier) completionQuotientHom
      (by sorry))

/-- Reducing the reconstructed homomorphism recovers each positive quotient map. -/
theorem Hom.baseRingHom_mk {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (n + 1))).comp a.baseRingHom =
      (a.quotientHom n).comp
        (Ideal.Quotient.mk (maximalIdeal η.base.carrier ^ (n + 1))) := sorry

/-- The reconstructed homomorphism of complete local rings is local. -/
theorem Hom.baseRingHom_isLocalHom {ξ η : FormalObject X} (a : Hom ξ η) :
    IsLocalHom a.baseRingHom := sorry

/-- The spectrum of the reconstructed homomorphism commutes with the structure maps. -/
theorem Hom.baseRingHom_over_S {ξ η : FormalObject X} (a : Hom ξ η) :
    Spec.map (CommRingCat.ofHom a.baseRingHom) ≫ η.base.toS = ξ.base.toS := sorry

/-- The morphism of complete local algebras determined by a compatible stage family. -/
def Hom.base {ξ η : FormalObject X} (a : Hom ξ η) :
    CompleteLocalSAlgebra.Hom ξ.base η.base where
  hom := a.baseRingHom
  isLocalHom := a.baseRingHom_isLocalHom
  over_S := a.baseRingHom_over_S

/-- Every stage map lifts the corresponding truncation of its reconstructed base map. -/
theorem Hom.over {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    X.p.IsHomLift (a.base.stageMap n) (a.app n) := sorry

/-- The base morphism is uniquely characterized by its lifted stage maps. -/
theorem Hom.base_unique {ξ η : FormalObject X} (a : Hom ξ η)
    (b : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (b.stageMap n) (a.app n)) : a.base = b := sorry

/-- Construct a natural stage family with a specified compatible base morphism. -/
def Hom.of {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) : Hom ξ η :=
  Hom.ofStages app naturality

/-- The reconstructed base of a family lifting a specified base is that specified base. -/
theorem Hom.of_base {ξ η : FormalObject X} (app : ∀ n, ξ.objects n ⟶ η.objects n)
    (base : CompleteLocalSAlgebra.Hom ξ.base η.base)
    (over : ∀ n, X.p.IsHomLift (base.stageMap n) (app n))
    (naturality : ∀ n, ξ.step n ≫ app (n + 1) = app n ≫ η.step n) :
    (Hom.of app base over naturality).base = base := sorry

/-- Identity natural transformation of a formal object. -/
def Hom.id (ξ : FormalObject X) : Hom ξ ξ := 𝟙 ξ.toFunctor

/-- Composition of natural stage families. -/
def Hom.comp {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ := a ≫ b

/-- The identity natural transformation has identity stage maps. -/
theorem Hom.id_app (ξ : FormalObject X) (n : ℕ) :
    (Hom.id ξ).app n = 𝟙 (ξ.objects n) := rfl

/-- Reconstruction takes identity stage maps to the identity base morphism. -/
theorem Hom.id_base (ξ : FormalObject X) :
    (Hom.id ξ).base = CompleteLocalSAlgebra.Hom.id ξ.base := sorry

/-- Composition of natural transformations is stagewise composition. -/
theorem Hom.comp_app {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) (n : ℕ) :
    (Hom.comp a b).app n = a.app n ≫ b.app n := rfl

/-- Reconstruction commutes with composition of compatible stage families. -/
theorem Hom.comp_base {ξ η ζ : FormalObject X} (a : Hom ξ η) (b : Hom η ζ) :
    (Hom.comp a b).base = CompleteLocalSAlgebra.Hom.comp a.base b.base := sorry

/-- Stage maps lift the reconstructed base and commute with successor transitions. -/
theorem Hom.spec {ξ η : FormalObject X} (a : Hom ξ η) (n : ℕ) :
    X.p.IsHomLift (a.base.stageMap n) (a.app n) ∧
      ξ.step n ≫ a.app (n + 1) = a.app n ≫ η.step n := by
  refine ⟨a.over n, ?_⟩
  have h := a.naturality (homOfLE (Nat.le_add_right n 1))
  dsimp only [toFunctor, Functor.ofSequence] at h
  rw [Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ] at h
  exact h

/-- The spectrum morphism induced by the reconstructed map on complete local rings. -/
def Hom.overMorphism {ξ η : FormalObject X} (a : Hom ξ η) :
    Spec (CommRingCat.of ξ.base.carrier) ⟶ Spec (CommRingCat.of η.base.carrier) :=
  a.base.toSpec

/-- The induced spectrum morphism is the spectrum of the reconstructed base homomorphism. -/
theorem Hom.overMorphism_eq {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism = a.base.toSpec := rfl

/-- The induced spectrum morphism is a morphism over the base scheme. -/
theorem Hom.liesOver {ξ η : FormalObject X} (a : Hom ξ η) :
    a.overMorphism ≫ η.base.toS = ξ.base.toS := a.base.over_S

end AlgebraicGeometry.GroupoidsOver.FormalObject
