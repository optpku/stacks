module

public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import stacks_project.Chap66.Definition_66_18_1_Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 96.4.2: associated-site notation such as 𝒳_étale, i.e.
`GroupoidsOver.etaleTopology`, is used only when 𝒳 is a category fibred in
groupoids, and not a scheme or algebraic space. This avoids confusion with the
small étale site X_étale of a scheme or algebraic space, i.e.
`Scheme.smallEtaleTopology` or `AlgebraicSpace.smallEtaleTopology` (roman
capital). -/
@[stacks 06TQ] #check
  (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦
    (X.etaleTopology : GrothendieckTopology X.total))
@[stacks 06TQ] #check
  (fun (X : Scheme.{u}) ↦ (X.smallEtaleTopology : GrothendieckTopology X.Etale))
@[stacks 06TQ] #check
  (fun {S : Scheme.{u}} (X : AlgebraicSpace S) ↦
    (AlgebraicSpace.smallEtaleTopology X :
      GrothendieckTopology (AlgebraicSpace.smallEtaleSite X)))
