module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
import ReasLib.AlgebraicGeometry.Scheme.Immersion
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

variable {Z X Z' X' : Scheme.{u}}
variable (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
variable [IsImmersion i] [IsImmersion i']
variable (sq : CommSq f i i' g)

/- Lemma 29.31.3: a commutative square of scheme immersions induces a canonical morphism from
the pullback of the upper conormal sheaf to the lower conormal sheaf. -/
@[stacks 01R4] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.map sq :
    (Scheme.Modules.pullback f).obj (Scheme.Hom.conormalSheaf i') ⟶
      Scheme.Hom.conormalSheaf i)

/- On cotangent generators, the canonical comparison is induced by the ambient structure map. -/
#check (AlgebraicGeometry.Scheme.Hom.Conormal.map_toCotangent sq)

/- The cotangent-generator formula uniquely characterizes the canonical comparison. -/
#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.existsUnique_map sq :
    ∃! tau : (Scheme.Modules.pullback f).obj (Scheme.Hom.conormalSheaf i') ⟶
        Scheme.Hom.conormalSheaf i,
      AlgebraicGeometry.Scheme.Hom.Conormal.IsMap sq tau)
