module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RepresentableSheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 80.3.11: if a presheaf `F` on schemes over `S` is a Zariski sheaf,
and an indexed family of fppf-sheaf subfunctors `H i` has algebraic-space-
representable inclusions and a coproduct map locally surjective for the fppf
topology, then `F` is an fppf sheaf. -/
@[stacks 07WE] #check
  (AlgebraicGeometry.isSheaf_fppfTopology_over_of_zariski_subfunctors :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F →
      ∀ {I : Type u} (H : I → Subfunctor F),
        (∀ i, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (H i).toFunctor) →
        (∀ i, AlgebraicSpace.representableByAlgebraicSpaces (H i).ι) →
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (Sigma.desc fun i ↦ (H i).ι) →
        Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
