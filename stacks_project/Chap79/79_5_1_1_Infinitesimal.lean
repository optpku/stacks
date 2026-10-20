module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap76.Lemma_76_9_8_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InfinitesimalSection

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- 79.5.1.1: The identity is an infinitesimal source section. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.InfinitesimalSection.id :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι], InfinitesimalSection G ι)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.InfinitesimalSection.toSection :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
    [AlgebraicSpace.IsFirstOrderThickening ι], InfinitesimalSection G ι → Section G)

end AlgebraicGeometry.GroupoidAlgebraicSpace
