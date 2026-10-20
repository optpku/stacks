module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 90.22.1: a groupoid in functors on `ArtinianLocalAlgCat Λ k` is prorepresentable
if it is isomorphic to the restriction of a representable groupoid in functors
`(coyoneda.obj (op R0), coyoneda.obj (op R1), s, t, c)` on `CompleteLocalAlgCat Λ k`. -/
@[stacks 06KD] #check (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff_restriction :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
    [Algebra Λ k] [Module.Finite Λ k]
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    GroupoidInFunctors.IsProrepresentable G ↔
      ∃ Ghat : GroupoidInFunctors.{u + 1, u, u} (CompleteLocalAlgCat Λ k),
        GroupoidInFunctors.IsRepresentable Ghat ∧
          Nonempty (GroupoidInFunctors.Iso (GroupoidInFunctors.restrictInclusion Ghat) G))
