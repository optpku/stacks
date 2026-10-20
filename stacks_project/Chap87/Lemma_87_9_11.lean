module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace Limits

universe u

/- Lemma 87.9.11: a map of presheaves from an affine formal algebraic space,
including its presentation size condition, that is representable by algebraic
spaces and locally quasi-finite is representable by schemes. -/
@[stacks 0AIG] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.relativelyRepresentable_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) [IsAffine X]
    (h_presentation :
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)
    (hf : representableByAlgebraicSpaces f)
    (h_locallyOfFiniteType :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyOfFiniteType (hf.pullbackHom ξ))
    (h_locallyQuasiFinite :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y), AlgebraicSpace.LocallyQuasiFinite (hf.pullbackHom ξ)),
    yoneda.relativelyRepresentable f)
