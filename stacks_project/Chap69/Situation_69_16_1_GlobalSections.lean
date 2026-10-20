module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections
import StacksCheckRecall

/-! The reusable global-sections ring API is provided by its mathematical owner. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (Presentation.tAppTop : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X),
  Γ(P.U.left, ⊤) ⟶ Γ(P.R.left.left, ⊤))
#check (Presentation.sAppTop : ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X),
  Γ(P.U.left, ⊤) ⟶ Γ(P.R.left.left, ⊤))
#check (chosenPresentation : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Presentation X)
/- Situation 69.16.1: We set A = Γ(X, 𝒪_X). -/
@[stacks 07UY] #check (AlgebraicGeometry.AlgebraicSpace.globalSectionsRing :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), CommRingCat.{u})
#check (globalSectionsRing_ofOver : ∀ {S : Scheme.{u}} (T : Over S),
  Nonempty (globalSectionsRing (ofOver T) ≅ Γ(T.left, ⊤)))

end AlgebraicGeometry.AlgebraicSpace
