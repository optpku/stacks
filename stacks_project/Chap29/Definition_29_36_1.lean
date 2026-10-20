module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/- Definition 29.36.1 (1): etaleness at a point is witnessed by compatible affine source and
target neighborhoods whose induced map on coordinate rings is etale. -/
@[stacks 02GI] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_exists_affineOpen f x :
    f.EtaleAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Etale)

/- Definition 29.36.1 (2): a scheme morphism is etale exactly when it is etale at every source
point. -/
@[stacks 02GI] #check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_forall_etaleAt f :
    AlgebraicGeometry.Etale f ↔ ∀ x : X, f.EtaleAt x)

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/- Definition 29.36.1 (3): a standard etale affine morphism is represented by a standard etale
algebra. -/
@[stacks 02GI] #check (Algebra.IsStandardEtale R A : Prop)

/- A standard etale pair records the monic polynomial, localization polynomial, and derivative
condition of a standard etale algebra. -/
#check (StandardEtalePair R : Type u)

/- A standard etale presentation identifies an algebra with the algebra associated to a standard
etale pair. -/
#check (StandardEtalePresentation R A : Type (max u v))

end AlgebraicGeometry
