module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ResidueField
import StacksCheckRecall

universe u

/- Lemma 29.20.5: if a morphism of schemes `f : X ⟶ S` is quasi-finite at a point `x : X`,
then the residue field extension `κ(x) / κ(f x)` is finite. -/
@[stacks 01TG] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt.moduleFinite_residueField :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {x : X},
      f.QuasiFiniteAt x →
        Module.Finite (S.residueField (f x)) (X.residueField x))
