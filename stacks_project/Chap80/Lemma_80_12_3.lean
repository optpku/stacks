module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothAtlas
import StacksCheckRecall

/-!
# Algebraic spaces from étale sheaves with a smooth scheme atlas

An étale sheaf on schemes over `S` whose diagonal is representable by algebraic
spaces, and which admits a surjective smooth map from a scheme over `S`, is an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.12.3: an étale sheaf on schemes over `S` whose diagonal is
representable by algebraic spaces and which admits a smooth surjective morphism
from a scheme over `S` is an algebraic space. -/
@[stacks 07WF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_etale_sheaf_smooth_surjective :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
      (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
      (hΔ : representableByAlgebraicSpaces (Limits.diag F)) {U : Over S}
      (p : yoneda.obj U ⟶ F),
      (representableByAlgebraicSpaces.of_diag hΔ p).has
        (@Surjective S ⊓ @Smooth S : MorphismProperty (AlgebraicSpace S)) →
      IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
