module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ChangeOfField
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (k l : Type u) [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/- Lemma 98.7.1 (1). A finite extension of the residue field induces the canonical
comparison of categories cofibered in groupoids over the Artinian local algebra base. -/
@[stacks 07WX] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.changeOfFieldFunctor k l openImmersion kToS h_factor X x0 :
    AlgebraicGeometry.GroupoidsOver.Predeformation.residueChangeBundled
      k l openImmersion kToS h_factor X x0 ⟶
    AlgebraicGeometry.GroupoidsOver.Predeformation.bundled openImmersion
      (AlgebraicGeometry.GroupoidsOver.Predeformation.lToS k l kToS)
      (AlgebraicGeometry.GroupoidsOver.Predeformation.lToS_factor k l openImmersion kToS h_factor) X
      (AlgebraicGeometry.GroupoidsOver.Predeformation.restrictResidue k l kToS X x0))

variable [HasRimSchlessinger X]

/- Lemma 98.7.1 (2). Under the Rim-Schlessinger condition the canonical comparison
is an equivalence over the Artinian local algebra base. -/
@[stacks 07WX] #check
  (AlgebraicGeometry.GroupoidsOver.Predeformation.changeOfField_isEquivalence
    k l openImmersion kToS h_factor X x0 :
    BasedFunctor.IsEquivalence
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (AlgebraicGeometry.GroupoidsOver.Predeformation.changeOfFieldFunctor k l openImmersion kToS h_factor X x0)))

end AlgebraicGeometry.GroupoidsOver.Predeformation
