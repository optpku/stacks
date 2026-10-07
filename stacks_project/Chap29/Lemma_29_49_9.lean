module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Domain
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/- The canonical morphism on the domain of a rational map represents that
rational map. -/
#check
  (AlgebraicGeometry.Scheme.RationalMap.toRationalMap_toPartialMap :
    ∀ {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y),
      φ.toPartialMap.toRationalMap = φ)

/- Lemma 29.49.9 (2): every morphism on the domain of a rational map that represents it equals
the morphism of its canonical partial-map representative. -/
@[stacks 0A1Y] #check
  (AlgebraicGeometry.Scheme.RationalMap.eq_toPartialMap_hom_of_toRationalMap :
    ∀ {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated] (φ : X ⤏ Y)
      (f : X.restrict φ.domain.isOpenEmbedding ⟶ Y),
      (⟨φ.domain, φ.dense_domain, f⟩ : X.PartialMap Y).toRationalMap = φ →
        f = φ.toPartialMap.hom)

/- Over a separated base, the canonical representative of a rational map
over the base is itself over the base. -/
#check
  (AlgebraicGeometry.Scheme.instIsOverToPartialMapOfIsSeparatedOfIsOver :
    ∀ {X Y S : Scheme.{u}} [IsReduced X] [Y.IsSeparated] [S.IsSeparated]
      [X.Over S] [Y.Over S] (φ : X ⤏ Y) [φ.IsOver S],
      φ.toPartialMap.IsOver S)

end AlgebraicGeometry
