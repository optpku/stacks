module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Restriction
import StacksCheckRecall

/-!
# Restriction of the sheaf of differentials of a morphism of algebraic spaces

Along an étale-vertical commutative square, the sheaf of relative differentials of
`f : X ⟶ Y` restricts on the small étale site of `U` to the sheaf of relative
differentials of `ψ : U ⟶ V`. When `U` and `V` are schemes, this agrees with the
usual Zariski sheaf of differentials of `U ⟶ V`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/- Lemma 76.7.3 (1): For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` and a
commutative square with étale vertical arrows `a : U ⟶ X` and `b : V ⟶ Y`,
`Modules.restrict (relativeDifferentials f) a` is isomorphic to `relativeDifferentials ψ`. -/
@[stacks 04CU] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.restrict_relativeDifferentials :
    ∀ {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : U ⟶ X) (b : V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a ψ f b),
    IsIsomorphic (Modules.restrict (relativeDifferentials f) a) (relativeDifferentials ψ))

/- Lemma 76.7.3 (2): If `U` and `V` are schemes, the restricted sheaf of differentials agrees
with `RingedSpace.Hom.differentials` of the morphism of schemes `U ⟶ V`. -/
@[stacks 04CU] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.restrict_relativeDifferentials_ofOver :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U V : Over S}
    (f : X ⟶ Y) (ψ : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    [Etale a] [Etale b] (sq : CommSq a (ofOverMap ψ) f b),
    IsIsomorphic
      ((Modules.restrictToScheme U).obj (Modules.restrict (relativeDifferentials f) a))
      (RingedSpace.Hom.differentials ψ.left.toShHom))

end Hom

end AlgebraicGeometry.AlgebraicSpace
