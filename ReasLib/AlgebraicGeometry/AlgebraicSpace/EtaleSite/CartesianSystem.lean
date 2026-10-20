module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Cocone

/-!
# Cartesian spaces-étale systems

An object of the 2-limit `lim_i X_{i,spaces,étale}` is a family of étale morphisms
`U_i ⟶ X_i` of algebraic spaces whose transition squares are cartesian. Pullback from
`spacesEtaleSite X` along a cocone `(X, X_i ⟶ X)` sends `U` to `U_i = X_i ×_X U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- A cartesian spaces-étale system over a diagram `D : J ⥤ Over B` is a family of étale
morphisms `U_i ⟶ X_i` of algebraic spaces such that every transition square is cartesian. -/
structure CartesianSpacesEtaleSystem.{u, v} {J : Type v} [Category.{v} J] {S : Scheme.{u}}
    {B : AlgebraicSpace S} (D : J ⥤ Over B) where
  /-- The diagram of algebraic spaces `i ↦ U_i`. -/
  functor : J ⥤ AlgebraicSpace S
  /-- The natural family of morphisms `U_i ⟶ X_i`. -/
  π : functor ⟶ D ⋙ Over.forget B
  /-- Each morphism `U_i ⟶ X_i` is étale. -/
  etale : ∀ i, Etale (π.app i)
  /-- Each transition square is a pullback. -/
  isPullback : ∀ {i j : J} (hij : i ⟶ j),
    IsPullback (functor.map hij) (π.app i) (π.app j) (D.map hij).left

universe u v

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- A cartesian spaces-étale system is pointwise étale, and every transition square is
cartesian. -/
theorem CartesianSpacesEtaleSystem.spec (U : CartesianSpacesEtaleSystem D) :
    (∀ i, Etale (U.π.app i)) ∧
      ∀ {i j : J} (hij : i ⟶ j),
        IsPullback (U.functor.map hij) (U.π.app i) (U.π.app j) (D.map hij).left :=
  ⟨U.etale, fun hij ↦ U.isPullback hij⟩

/-- A morphism of cartesian spaces-étale systems over `D` is a natural transformation of the
`U_i` commuting with the projections to the `X_i`. -/
structure CartesianSpacesEtaleSystem.Hom (U V : CartesianSpacesEtaleSystem D) where
  /-- The underlying natural transformation `U_i ⟶ V_i`. -/
  nat : U.functor ⟶ V.functor
  /-- Each component is a morphism over `X_i`. -/
  w : ∀ i, nat.app i ≫ V.π.app i = U.π.app i

/-- The identity morphism of a cartesian spaces-étale system. -/
def CartesianSpacesEtaleSystem.Hom.id (U : CartesianSpacesEtaleSystem D) :
    CartesianSpacesEtaleSystem.Hom U U where
  nat := 𝟙 U.functor
  w _ := Category.id_comp _

/-- Composition of compatible natural transformations of cartesian spaces-étale systems. -/
def CartesianSpacesEtaleSystem.Hom.comp {U V W : CartesianSpacesEtaleSystem D}
    (f : CartesianSpacesEtaleSystem.Hom U V) (g : CartesianSpacesEtaleSystem.Hom V W) :
    CartesianSpacesEtaleSystem.Hom U W where
  nat := f.nat ≫ g.nat
  w i := by
    change (f.nat.app i ≫ g.nat.app i) ≫ W.π.app i = U.π.app i
    rw [Category.assoc, g.w, f.w]

/-- The comparison morphism of pullbacks `X_i ×_X U ⟶ X_j ×_X U` along `hij : i ⟶ j`. -/
def spacesEtalePullbackMap (c : Cocone D) {U : AlgebraicSpace S} (f : U ⟶ c.pt.left)
    {i j : J} (hij : i ⟶ j) :
    overPullbackObj f (Over.mk (c.ι.app i).left) ⟶
      overPullbackObj f (Over.mk (c.ι.app j).left) :=
  overPullbackMap f ((toOverApex c).map hij)

/-- The diagram `i ↦ X_i ×_X U` of sheaf fibre products along a cocone in `Over B`. -/
def spacesEtalePullbackDiagram (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) : J ⥤ AlgebraicSpace S where
  obj i := overPullbackObj f (Over.mk (c.ι.app i).left)
  map hij := spacesEtalePullbackMap c f hij
  map_id i := by
    change overPullbackMap f ((toOverApex c).map (𝟙 i)) = _
    rw [(toOverApex c).map_id]
    exact overPullbackMap_id f _
  map_comp hij hjk := by
    change overPullbackMap f ((toOverApex c).map (hij ≫ hjk)) = _
    rw [(toOverApex c).map_comp]
    exact overPullbackMap_comp f _ _

/-- The object of `spacesEtalePullbackDiagram c f` at `i` is the fibre product `X_i ×_X U`. -/
theorem spacesEtalePullbackDiagram_obj (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) (i : J) :
    (spacesEtalePullbackDiagram c f).obj i =
      overPullbackObj f (Over.mk (c.ι.app i).left) :=
  rfl

/-- The first projections of the pullback diagram are natural in the indexing morphisms. -/
theorem spacesEtalePullbackFst_naturality (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) {i j : J} (hij : i ⟶ j) :
    spacesEtalePullbackMap c f hij ≫ overPullbackFst f (Over.mk (c.ι.app j).left) =
      overPullbackFst f (Over.mk (c.ι.app i).left) ≫ (D.map hij).left :=
  sorry

/-- Pullback of an étale morphism has étale first projections. -/
theorem spacesEtalePullbackFst_etale (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) (hf : Etale f) (i : J) :
    Etale (overPullbackFst f (Over.mk (c.ι.app i).left)) :=
  sorry

/-- The transition squares of the canonical pullback diagram are cartesian. -/
theorem spacesEtalePullbackMap_isPullback (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) {i j : J} (hij : i ⟶ j) :
    IsPullback (spacesEtalePullbackMap c f hij)
      (overPullbackFst f (Over.mk (c.ι.app i).left))
      (overPullbackFst f (Over.mk (c.ι.app j).left)) (D.map hij).left :=
  sorry

/-- The cartesian spaces-étale system obtained by pulling back an étale morphism `U ⟶ X` along
the cocone legs `X_i ⟶ X`. -/
def ofSpacesEtalePullback (c : Cocone D) (U : spacesEtaleSite c.pt.left) :
    CartesianSpacesEtaleSystem D where
  functor := spacesEtalePullbackDiagram c U.hom
  π :=
    { app := fun i ↦ overPullbackFst U.hom (Over.mk (c.ι.app i).left)
      naturality := fun _ _ hij ↦ spacesEtalePullbackFst_naturality c U.hom hij }
  etale i := spacesEtalePullbackFst_etale c U.hom U.prop i
  isPullback hij := spacesEtalePullbackMap_isPullback c U.hom hij

/-- The object of `ofSpacesEtalePullback c U` at `i` is the fibre product `X_i ×_X U`. -/
theorem ofSpacesEtalePullback_obj (c : Cocone D) (U : spacesEtaleSite c.pt.left) (i : J) :
    (ofSpacesEtalePullback c U).functor.obj i =
      overPullbackObj U.hom (Over.mk (c.ι.app i).left) :=
  rfl

/-- The projection of `ofSpacesEtalePullback c U` at `i` is `overPullbackFst`. -/
theorem ofSpacesEtalePullback_π (c : Cocone D) (U : spacesEtaleSite c.pt.left) (i : J) :
    (ofSpacesEtalePullback c U).π.app i =
      overPullbackFst U.hom (Over.mk (c.ι.app i).left) :=
  rfl

/-- The two projections of `X_i ×_X U` and the map `U ⟶ V` over `X` form a cone over `X`. -/
theorem spacesEtaleInducedMap_w (c : Cocone D) {U V : spacesEtaleSite c.pt.left}
    (f : U ⟶ V) (i : J) :
    overPullbackFst U.hom (Over.mk (c.ι.app i).left) ≫ (c.ι.app i).left =
      (overPullbackSnd U.hom (Over.mk (c.ι.app i).left) ≫ f.left) ≫ V.hom :=
  sorry

/-- The comparison morphism `X_i ×_X U ⟶ X_i ×_X V` induced by a morphism over `X`. -/
def spacesEtaleInducedMap (c : Cocone D) {U V : spacesEtaleSite c.pt.left} (f : U ⟶ V)
    (i : J) :
    overPullbackObj U.hom (Over.mk (c.ι.app i).left) ⟶
      overPullbackObj V.hom (Over.mk (c.ι.app i).left) :=
  ReasLibPullback.pullbackLift (c.ι.app i).left V.hom
    (overPullbackFst U.hom (Over.mk (c.ι.app i).left))
    (overPullbackSnd U.hom (Over.mk (c.ι.app i).left) ≫ f.left)
    (spacesEtaleInducedMap_w c f i)

/-- The maps induced by a morphism over the apex are natural in the diagram. -/
theorem spacesEtaleInducedMap_naturality (c : Cocone D)
    {U V : spacesEtaleSite c.pt.left} (f : U ⟶ V) {i j : J} (hij : i ⟶ j) :
    spacesEtalePullbackMap c U.hom hij ≫ spacesEtaleInducedMap c f j =
      spacesEtaleInducedMap c f i ≫ spacesEtalePullbackMap c V.hom hij :=
  sorry

/-- The induced map of pullbacks preserves the first projections. -/
theorem spacesEtaleInducedMap_fst (c : Cocone D)
    {U V : spacesEtaleSite c.pt.left} (f : U ⟶ V) (i : J) :
    spacesEtaleInducedMap c f i ≫ overPullbackFst V.hom (Over.mk (c.ι.app i).left) =
      overPullbackFst U.hom (Over.mk (c.ι.app i).left) :=
  sorry

/-- The morphism of cartesian spaces-étale systems induced by a morphism in
`spacesEtaleSite X`. -/
def inducedHom (c : Cocone D) {U V : spacesEtaleSite c.pt.left} (f : U ⟶ V) :
    CartesianSpacesEtaleSystem.Hom (ofSpacesEtalePullback c U)
      (ofSpacesEtalePullback c V) where
  nat :=
    { app := fun i ↦ spacesEtaleInducedMap c f i
      naturality := fun _ _ hij ↦ spacesEtaleInducedMap_naturality c f hij }
  w := fun i ↦ spacesEtaleInducedMap_fst c f i

/-- The component of `inducedHom c f` at `i` is `spacesEtaleInducedMap c f i`. -/
theorem inducedHom_app (c : Cocone D) {U V : spacesEtaleSite c.pt.left} (f : U ⟶ V)
    (i : J) :
    (inducedHom c f).nat.app i = spacesEtaleInducedMap c f i :=
  rfl

/-- A cartesian spaces-étale system lies in the essential image of pullback from
`spacesEtaleSite X` when it is isomorphic over `D` to `ofSpacesEtalePullback c U` for some
`U` étale over `X`. -/
def IsInSpacesEtaleEssImage (c : Cocone D) (sys : CartesianSpacesEtaleSystem D) : Prop :=
  ∃ (U : spacesEtaleSite c.pt.left)
    (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
    sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π

/-- Essential-image membership is an isomorphism over `D` with a pullback from
`spacesEtaleSite X`. -/
theorem isInSpacesEtaleEssImage_iff (c : Cocone D) (sys : CartesianSpacesEtaleSystem D) :
    IsInSpacesEtaleEssImage c sys ↔
      ∃ (U : spacesEtaleSite c.pt.left)
        (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
        sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π :=
  Iff.rfl

/-- The base-change functor `U ↦ (X_i ×_X U)` from `spacesEtaleSite X` to cartesian
spaces-étale systems over `D` is an equivalence: it is fully faithful on morphisms, and every
cartesian system lies in its essential image. -/
def IsSpacesEtalePullbackEquivalence (c : Cocone D) : Prop :=
  (∀ (U V : spacesEtaleSite c.pt.left),
      Function.Bijective (fun f : U ⟶ V ↦ inducedHom c f)) ∧
    ∀ sys : CartesianSpacesEtaleSystem D, IsInSpacesEtaleEssImage c sys

/-- Equivalence of the spaces-étale base-change functor is fully faithfulness of `inducedHom`
together with essential surjectivity onto cartesian systems. -/
theorem isSpacesEtalePullbackEquivalence_iff (c : Cocone D) :
    IsSpacesEtalePullbackEquivalence c ↔
      (∀ (U V : spacesEtaleSite c.pt.left),
          Function.Bijective (fun f : U ⟶ V ↦ inducedHom c f)) ∧
        ∀ sys : CartesianSpacesEtaleSystem D, IsInSpacesEtaleEssImage c sys :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
