module

public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.RingTheory.RingHom.SquareZero.Split
public import ReasLib.RingTheory.RingHom.SquareZero.IsoClass

/-!
# Tangent classes and infinitesimal automorphisms of flat algebras

The dual-number fibre of the residue slice classifies first-order flat algebra
extensions. Its tangent classes are parametrized by naive cotangent Ext¹, and
the automorphisms of its trivial object are parametrized by derivations.
-/

@[expose] public section

open CategoryTheory Functor ArtinianLocalAlgCat TrivSqZeroExt
open RingHom.SquareZeroExtension

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

set_option backward.privateInPublic true


/-- The derivation-induced endomorphism commutes with the dual-number coefficient map. -/
private theorem idAddEpsilonHom_commutes
    (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    (DualNumber.autOfDerivation D).toRingHom.comp
        (algebraMap (trivialDeformationObj Λ k P).base.carrier (trivialDeformationObj Λ k P).algebra) =
      (algebraMap (trivialDeformationObj Λ k P).base.carrier (trivialDeformationObj Λ k P).algebra).comp
        (ArtinianLocalAlgCat.Hom.hom (𝟙 (dualNumber Λ k))).toRingHom := sorry

/-- The derivation-induced endomorphism induces a base-change isomorphism. -/
private theorem idAddEpsilonHom_isIsoTensor
    (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    Function.Bijective (canonicalTensorMap
      (Q := trivialDeformationObj Λ k P) (P := trivialDeformationObj Λ k P)
      (𝟙 (dualNumber Λ k)) (DualNumber.autOfDerivation D).toRingHom
      (idAddEpsilonHom_commutes Λ k P D)) := sorry

/-- The endomorphism of the trivial flat algebra induced by a derivation. -/
def idAddEpsilonHom (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    trivialDeformationObj Λ k P ⟶ trivialDeformationObj Λ k P :=
  Hom.of (𝟙 (dualNumber Λ k)) (DualNumber.autOfDerivation D).toRingHom
    (by exact idAddEpsilonHom_commutes Λ k P D) (by exact idAddEpsilonHom_isIsoTensor Λ k P D)

/-- The underlying ring map of the derivation-induced flat algebra endomorphism. -/
theorem idAddEpsilonHom_toRingHom (P : Type u) [CommRing P] [Algebra k P]
    (D : Derivation k P P) :
    (idAddEpsilonHom Λ k P D).toRingHom = (DualNumber.autOfDerivation D).toRingHom := rfl

/-- The derivation-induced endomorphism reduces to the identity on the residue algebra. -/
private theorem infEndOfDerivation_over
    (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    idAddEpsilonHom Λ k P D ≫ trivialDeformationToResidue Λ k P =
      trivialDeformationToResidue Λ k P := sorry

/-- The derivation-induced endomorphism in the dual-number fibre of the residue slice. -/
private def infEndOfDerivation
    (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    trivialDeformationFiber Λ k P ⟶ trivialDeformationFiber Λ k P :=
  let f : trivialDeformationOver Λ k P ⟶ trivialDeformationOver Λ k P :=
    Over.homMk (idAddEpsilonHom Λ k P D) (infEndOfDerivation_over Λ k P D)
  ⟨f, by
    change (deformationForget Λ k P).IsHomLift ((deformationForget Λ k P).map f) f
    exact IsHomLift.map _ _⟩

/-- Opposite derivations induce mutually inverse endomorphisms in the residue slice fibre. -/
private theorem infEndOfDerivation_comp_neg
    (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    infEndOfDerivation Λ k P D ≫ infEndOfDerivation Λ k P (-D) =
      𝟙 (trivialDeformationFiber Λ k P) := sorry

/-- A derivation gives an automorphism of the trivial dual-number deformation reducing to
identity on the residue algebra, with inverse induced by its negative. -/
def infAutOfDerivation (P : Type u) [CommRing P] [Algebra k P] (D : Derivation k P P) :
    Aut (trivialDeformationFiber Λ k P) where
  hom := by exact infEndOfDerivation Λ k P D
  inv := by exact infEndOfDerivation Λ k P (-D)
  hom_inv_id := by exact infEndOfDerivation_comp_neg Λ k P D
  inv_hom_id := by simpa only [neg_neg] using infEndOfDerivation_comp_neg Λ k P (-D)

/-- Addition of derivations corresponds to composition of infinitesimal automorphisms. -/
theorem infAutOfDerivation_map_add (P : Type u) [CommRing P] [Algebra k P]
    (D E : Derivation k P P) :
    infAutOfDerivation Λ k P (D + E) =
      infAutOfDerivation Λ k P D * infAutOfDerivation Λ k P E := sorry

/-- The dual-number kernel coefficient is mapped to the coefficient algebra. -/
private def kernelToAlgebra (P : Type u) [CommRing P] [Algebra k P] :
    KernelModule (fstHom k k k).toRingHom →ₗ[k] P :=
  (Algebra.linearMap k P).comp (RingHom.SquareZeroExtension.kernelEquiv_fst k k).toLinearMap

/-- The coefficient map applies the algebra map to the infinitesimal coordinate. -/
private theorem kernelToAlgebra_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : KernelModule (fstHom k k k).toRingHom) :
    kernelToAlgebra k P x = algebraMap k P (val x).snd := rfl

/-- The coefficientwise dual-number map commutes with the first projections. -/
private theorem trivialSolution_comm_right (P : Type u) [CommRing P] [Algebra k P] :
    (fstHom P P P).toRingHom.comp (dualNumberRingHom Λ k P) =
      (structureMap : k →+* P).comp (fstHom k k k).toRingHom := sorry

/-- The trivial dual-number extension induces the coefficient algebra map on kernels. -/
private theorem trivialSolution_induces (P : Type u) [CommRing P] [Algebra k P] :
    ∀ x : KernelModule (fstHom k k k).toRingHom,
      RingHom.SquareZeroExtension.kernelEquiv_fst P P
        (kerMapOf (fstHom k k k).toRingHom (dualNumberRingHom Λ k P)
          (fstHom P P P).toRingHom (trivialSolution_comm_right Λ k P) x) =
        kernelToAlgebra k P x := sorry

/-- The trivial square-zero solution over the dual-number coefficient projection has
middle ring the dual numbers of the coefficient algebra. -/
def trivialSolution (P : Type u) [CommRing P] [Algebra k P] :
    Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P) :=
  Solution.of (fstHom k k k).toRingHom (kernelToAlgebra k P)
    (dualNumberRingHom Λ k P) (fstHom P P P).toRingHom
    (by exact trivialSolution_comm_right Λ k P) (RingHom.SquareZeroExtension.kernelEquiv_fst P P)
    (by exact trivialSolution_induces Λ k P)

/-- The carrier of the trivial square-zero solution is the dual-number ring. -/
theorem trivialSolution_carrier (P : Type u) [CommRing P] [Algebra k P] :
    (trivialSolution Λ k P).carrier = DualNumber P := rfl

/-- A square-zero solution inducing the coefficient algebra map is flat over the dual numbers. -/
private theorem ofSolution_flat (P : Type u) [CommRing P] [Algebra k P]
    (S : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    -- Local instance justification (proof-local temporary data): unpack the stored explicit ring structure of the solution.
    letI := S.commRing
    -- Local instance justification (noncanonical choice): the dual-number algebra on the solution carrier is determined by its structure morphism.
    letI : Algebra (dualNumber Λ k).carrier S.carrier := S.fromA'.toAlgebra
    Module.Flat (dualNumber Λ k).carrier S.carrier := sorry

/-- The projection of a square-zero solution commutes with the residue coefficient map. -/
private theorem ofSolution_commutes (P : Type u) [CommRing P] [Algebra k P]
    (S : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    -- Local instance justification (proof-local temporary data): unpack the stored explicit ring structure of the solution.
    letI := S.commRing
    -- Local instance justification (noncanonical choice): the dual-number algebra on the solution carrier is determined by its structure morphism.
    letI : Algebra (dualNumber Λ k).carrier S.carrier := S.fromA'.toAlgebra
    S.toB.comp (algebraMap (dualNumber Λ k).carrier S.carrier) =
      (algebraMap (ofResidue Λ k P).base.carrier (ofResidue Λ k P).algebra).comp
        (ArtinianLocalAlgCat.dualNumberToResidue Λ k).hom.toRingHom := sorry

/-- The residue projection of a square-zero solution induces a base-change isomorphism. -/
private theorem ofSolution_isIsoTensor (P : Type u) [CommRing P] [Algebra k P]
    (S : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    -- Local instance justification (proof-local temporary data): unpack the stored explicit ring structure of the solution.
    letI := S.commRing
    -- Local instance justification (noncanonical choice): the dual-number algebra on the solution carrier is determined by its structure morphism.
    letI : Algebra (dualNumber Λ k).carrier S.carrier := S.fromA'.toAlgebra
    -- Local instance justification (proof-local temporary data): flatness is supplied by the law for this explicit solution.
    letI : Module.Flat (dualNumber Λ k).carrier S.carrier := by exact ofSolution_flat Λ k P S
    Function.Bijective (canonicalTensorMap
      (Q := of (dualNumber Λ k) S.carrier) (P := ofResidue Λ k P)
      (ArtinianLocalAlgCat.dualNumberToResidue Λ k) S.toB
      (ofSolution_commutes Λ k P S)) := sorry

/-- A square-zero solution defines the isomorphism class of a flat dual-number deformation. -/
def ofSolution (P : Type u) [CommRing P] [Algebra k P]
    (S : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    Functor.tangentSpace (deformationForget Λ k P) :=
  -- Local instance justification (proof-local temporary data): unpack the stored explicit ring structure of the solution.
  letI := S.commRing
  -- Local instance justification (noncanonical choice): the dual-number algebra on the solution carrier is determined by its structure morphism.
  letI : Algebra (dualNumber Λ k).carrier S.carrier := S.fromA'.toAlgebra
  -- Local instance justification (proof-local temporary data): flatness is supplied by the law for this explicit solution.
  letI : Module.Flat (dualNumber Λ k).carrier S.carrier := by exact ofSolution_flat Λ k P S
  let hom : of (dualNumber Λ k) S.carrier ⟶ ofResidue Λ k P :=
    Hom.of (ArtinianLocalAlgCat.dualNumberToResidue Λ k) S.toB
      (ofSolution_commutes Λ k P S) (by exact ofSolution_isIsoTensor Λ k P S)
  tangentSpace.mk (deformationForget Λ k P)
    (Fiber.mk (rfl : (deformationForget Λ k P).obj (Over.mk hom) = dualNumber Λ k))

/-- Two solutions determine the same tangent class exactly when they admit a fitting map
of their identity connecting diagram. -/
theorem ofSolution_iso_iff (P : Type u) [CommRing P] [Algebra k P]
    (S T : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    ofSolution Λ k P S = ofSolution Λ k P T ↔ Nonempty (FittingMap (compare S T)) := sorry

/-- The solution-to-deformation map descends to isomorphism classes of solutions. -/
def ofIsoClass (P : Type u) [CommRing P] [Algebra k P] :
    IsoClass (fstHom k k k).toRingHom P (kernelToAlgebra k P) →
      Functor.tangentSpace (deformationForget Λ k P) :=
  Quotient.lift (ofSolution Λ k P) (fun S T h ↦ (ofSolution_iso_iff Λ k P S T).mpr h)

/-- The map on isomorphism classes agrees with the map on solution representatives. -/
theorem ofIsoClass_mk (P : Type u) [CommRing P] [Algebra k P]
    (S : Solution (B := P) (N := P) (fstHom k k k).toRingHom (kernelToAlgebra k P)) :
    ofIsoClass Λ k P (isoClassMk S) = ofSolution Λ k P S := rfl

/-- A naive cotangent Ext¹ class defines a tangent class through the chart based at the
trivial dual-number solution. -/
def ofExtClass (P : Type u) [CommRing P] [Algebra k P]
    (ξ : extOneNaiveCotangent k P P) :
    Functor.tangentSpace (deformationForget Λ k P) :=
  ofIsoClass Λ k P (isoClassEquiv (trivialSolution Λ k P) ξ)

/-- The zero Ext¹ class represents the trivial dual-number deformation. -/
theorem ofExtClass_zero (P : Type u) [CommRing P] [Algebra k P] :
    ofExtClass Λ k P 0 =
      tangentSpace.mk (deformationForget Λ k P) (trivialDeformationFiber Λ k P) := sorry

/-- Naive cotangent Ext¹ classes bijectively parametrize flat dual-number deformation classes. -/
theorem ofExtClass_bijective (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (ofExtClass Λ k P) := sorry

/-- Derivations bijectively parametrize automorphisms of the trivial dual-number deformation
that reduce to the identity on the residue algebra. -/
theorem infAutOfDerivation_bijective (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (infAutOfDerivation Λ k P) := sorry

end FlatAlgebraCat
