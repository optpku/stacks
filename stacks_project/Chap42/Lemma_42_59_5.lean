module

public import stacks_project.Chap42.Definition_42_59_4
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle Gysin

/- Lemma 42.59.5: in Situation 42.7.1, if `f : X ⟶ Y` is a local complete intersection
morphism of schemes locally of finite type over `S`, the Gysin map exists for `f`, and `f` is
flat, then the Gysin class of `f` equals the flat-pullback bivariant class of Lemma 42.33.2.
The displayed immersion–smooth factorization witnesses existence of the Gysin map.
Regularity and availability of a normal-sheaf deformation realization are conclusions,
rather than extra hypotheses. Equality of the integer-degree families includes varying
normal ranks and relative dimensions; independence of the realization is supplied by
`gysin_eq_of_factorization`. -/
@[stacks 0FF4] #check
  (AlgebraicGeometry.BivariantClass.gysin_eq_flatPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [Flat f.left] {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) [IsImmersion i.left] [hg : Smooth g.left]
    (hfac : i ≫ g = f),
    ∃ hreg : IsRegularImmersion i.left,
    ∃ e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left,
    ∃ D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (@normalBundle X.left P.left i.left hreg e).toCoborder,
      (fun p : ℤ ↦ @factorizationClassDegree S inferInstance δ inferInstance X Y P
        inferInstance inferInstance inferInstance f i g hreg hg hfac e D p) =
        (fun p : ℤ ↦ flatPullbackDegree δ f p))

end AlgebraicGeometry.BivariantClass
