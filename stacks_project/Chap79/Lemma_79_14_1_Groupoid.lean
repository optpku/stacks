module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.FinitePart
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.ArrowPoint :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}, GroupoidAlgebraicSpace B → Over S → Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.finitePartHom :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left],
    Hom (finitePart G) G)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.map_s :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H), G.s ≫ f.obj = f.arrow ≫ H.s)

end AlgebraicGeometry.GroupoidAlgebraicSpace
