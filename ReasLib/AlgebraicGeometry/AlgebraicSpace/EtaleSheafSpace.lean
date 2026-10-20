module

public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Logic.Small.Defs
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos

/-!
# Algebraic space associated to an étale sheaf of sets

A sheaf of sets `F` on `Y_étale` determines a functor of points whose value on a
scheme `T` over `S` is the type of pairs `(y, s)` with `y : T ⟶ Y` over `S` and
`s ∈ Γ(T, y_small⁻¹ F)`. Under a smallness hypothesis this functor is an algebraic
space étale over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S}

/-- The identity object of the small étale site of a scheme `T` over `S`. -/
def smallEtaleSite.id (T : Over S) : smallEtaleSite (ofOver T) :=
  smallEtaleSite.mk (𝟙 (ofOver T))

/-- Global sections of the inverse image of `F` along `y_small`, evaluated at the identity
object of `T_étale`. -/
def etaleInverseImageSections {T : Over S} (y : ofOver T ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) : Type (u + 1) :=
  ((smallEtaleMorphismOfTopoi y).inverseImage.obj F).obj.obj
    (op (smallEtaleSite.id T))

/-- `etaleInverseImageSections y F` is evaluation of `y_small⁻¹ F` at
`smallEtaleSite.id T`. -/
theorem etaleInverseImageSections_def {T : Over S} (y : ofOver T ⟶ Y)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    etaleInverseImageSections y F =
      ((smallEtaleMorphismOfTopoi y).inverseImage.obj F).obj.obj
        (op (smallEtaleSite.id T)) :=
  rfl

/-- The unique morphism in `T_étale` from an étale scheme over `T` to the identity object. -/
def smallEtaleSite.homToId (T : Over S) (U : smallEtaleSite (ofOver T)) :
    U ⟶ smallEtaleSite.id T :=
  MorphismProperty.CostructuredArrow.homMk (yoneda.preimage U.hom) trivial sorry

/-- A compatible family of sections of `y_small⁻¹ F` obtained by restricting a global
section along `smallEtaleSite.homToId`. -/
def etaleInverseImageSections.toFamily {T : Over S} {y : ofOver T ⟶ Y}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (s : etaleInverseImageSections y F) :
    ((smallEtaleMorphismOfTopoi y).inverseImage.obj F).obj.sections :=
  ⟨fun U ↦
    ((smallEtaleMorphismOfTopoi y).inverseImage.obj F).obj.map
      (smallEtaleSite.homToId T U.unop).op s,
    sorry⟩

/-- Restriction of a global section of `y_small⁻¹ F` along `g : T' ⟶ T`, using
`smallEtaleMorphismOfTopoiComp` and inverse image of the terminal sheaf. -/
def etaleInverseImageSections.restrict {T T' : Over S} (g : T' ⟶ T) {y : ofOver T ⟶ Y}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (s : etaleInverseImageSections y F) :
    etaleInverseImageSections ((ofOverFunctor S).map g ≫ y) F :=
  let G := (smallEtaleMorphismOfTopoi y).inverseImage.obj F
  let gAS := (ofOverFunctor S).map g
  let fTop := smallEtaleMorphismOfTopoi gAS
  let sHom := Sheaf.sectionsTerminalHomEquiv G (etaleInverseImageSections.toFamily F s)
  let pulled := fTop.inverseImageTerminalIso.inv ≫ fTop.inverseImage.map sHom
  let sFam := (Sheaf.sectionsTerminalHomEquiv (fTop.inverseImage.obj G)).symm pulled
  ((smallEtaleMorphismOfTopoiComp gAS y).app F).inv.hom.app
    (op (smallEtaleSite.id T'))
    (sFam.1 (op (smallEtaleSite.id T')))

/-- A `T`-point of the functor associated to `F`: a morphism `y : T ⟶ Y` over `S` together
with a global section of `y_small⁻¹ F`. -/
abbrev sheafSpacePair (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (T : Over S) :=
  (y : ofOver T ⟶ Y) × etaleInverseImageSections y F

/-- Constructor for a pair `(y, s)` associated to `F`. -/
def sheafSpacePair.mk (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) {T : Over S}
    (y : ofOver T ⟶ Y) (s : etaleInverseImageSections y F) : sheafSpacePair F T :=
  ⟨y, s⟩

/-- Restriction of a pair along `g : T' ⟶ T` sends `(y, s)` to
`(y ∘ g, g_small⁻¹ s)`. -/
def sheafSpacePair.restrict {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (p : sheafSpacePair F T) : sheafSpacePair F T' :=
  ⟨(ofOverFunctor S).map g ≫ p.1, etaleInverseImageSections.restrict g F p.2⟩

/-- The first component of `sheafSpacePair.mk y s` is `y`. -/
theorem sheafSpacePair.mk_fst (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) {T : Over S}
    (y : ofOver T ⟶ Y) (s : etaleInverseImageSections y F) :
    (sheafSpacePair.mk F y s).1 = y :=
  rfl

/-- The second component of `sheafSpacePair.mk y s` is `s`. -/
theorem sheafSpacePair.mk_snd (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) {T : Over S}
    (y : ofOver T ⟶ Y) (s : etaleInverseImageSections y F) :
    (sheafSpacePair.mk F y s).2 = s :=
  rfl

/-- Restriction of pairs postcomposes the morphism to `Y` with `ofOverFunctor.map g`. -/
theorem sheafSpacePair.restrict_fst {T T' : Over S} (g : T' ⟶ T)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (p : sheafSpacePair F T) :
    (sheafSpacePair.restrict g F p).1 = (ofOverFunctor S).map g ≫ p.1 :=
  rfl

/-- The set-theoretic smallness hypothesis on the functor associated to `F`: each type of
pairs `sheafSpacePair F T` is `u`-small. -/
def IsEtaleSheafSmall (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) : Prop :=
  ∀ T : Over S, Small.{u} (sheafSpacePair F T)

/-- `IsEtaleSheafSmall F` means that `sheafSpacePair F T` is `u`-small for every scheme
`T` over `S`. -/
theorem isEtaleSheafSmall_iff (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    IsEtaleSheafSmall F ↔ ∀ T : Over S, Small.{u} (sheafSpacePair F T) :=
  Iff.rfl

/-- The functor of points associated to `F`, with values shrunk to universe `u`. -/
def sheafSpaceFunctor (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : (Over S)ᵒᵖ ⥤ Type u := by
  refine
    { obj T := @Shrink.{u} (sheafSpacePair F T.unop) (h T.unop)
      map {T T'} g :=
        TypeCat.ofHom fun p ↦
          @equivShrink.{u} (sheafSpacePair F T'.unop) (h T'.unop)
            (sheafSpacePair.restrict g.unop F
              ((@equivShrink.{u} (sheafSpacePair F T.unop) (h T.unop)).symm p))
      map_id := ?_
      map_comp := ?_ }
  all_goals sorry

/-- Values of `sheafSpaceFunctor F h` are equivalent to pairs `(y, s)`. -/
def sheafSpaceFunctor_obj_equiv (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (T : Over S) :
    (sheafSpaceFunctor F h).obj (op T) ≃ sheafSpacePair F T :=
  (@equivShrink.{u} (sheafSpacePair F T) (h T)).symm

/-- `sheafSpaceFunctor_obj_equiv` is the inverse of `equivShrink`. -/
theorem sheafSpaceFunctor_obj_equiv_apply (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) {T : Over S} (p : (sheafSpaceFunctor F h).obj (op T)) :
    sheafSpaceFunctor_obj_equiv F h T p =
      (@equivShrink.{u} (sheafSpacePair F T) (h T)).symm p :=
  rfl

/-- The algebraic space associated to an étale sheaf of sets, under the smallness
hypothesis `IsEtaleSheafSmall F`. -/
def sheafSpace (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F) :
    AlgebraicSpace S :=
  by
    refine ofFunctor (sheafSpaceFunctor F h) ?_ ?_ ?_
    all_goals sorry

/-- The functor of points of `sheafSpace F h` is `sheafSpaceFunctor F h`. -/
theorem sheafSpace_functorOfPoints (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    (sheafSpace F h).functorOfPoints = sheafSpaceFunctor F h :=
  rfl

/-- `sheafSpace F h` is an fppf sheaf with representable diagonal and a representable étale
locally-surjective atlas. -/
theorem sheafSpace_spec (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafSpace F h).functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (sheafSpace F h).functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (sheafSpace F h).functorOfPoints),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  sorry

/-- The morphism `ofOver T ⟶ sheafSpace F h` associated to a pair `(y, s)`. -/
def sheafSpace.homOfPair (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) {T : Over S} (p : sheafSpacePair F T) :
    ofOver T ⟶ sheafSpace F h :=
  yonedaEquiv.symm ((@equivShrink.{u} (sheafSpacePair F T) (h T)) p)

/-- `sheafSpace.homOfPair` is the Yoneda inverse of the shrunk pair. -/
theorem sheafSpace.homOfPair_eq (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) {T : Over S} (p : sheafSpacePair F T) :
    sheafSpace.homOfPair F h p =
      yonedaEquiv.symm ((@equivShrink.{u} (sheafSpacePair F T) (h T)) p) :=
  rfl

/-- The projection `sheafSpace F h ⟶ Y` forgetting the section of `F`. -/
def sheafSpaceTo (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : sheafSpace F h ⟶ Y where
  app T :=
    TypeCat.ofHom fun p ↦
      yonedaEquiv ((@equivShrink.{u} (sheafSpacePair F T.unop) (h T.unop)).symm p).1
  naturality := sorry

/-- Components of `sheafSpaceTo F h` send a shrunk pair to the underlying morphism `T ⟶ Y`. -/
theorem sheafSpaceTo_app (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) (T : (Over S)ᵒᵖ)
    (p : (sheafSpace F h).functorOfPoints.obj T) :
    (sheafSpaceTo F h).app T p =
      yonedaEquiv ((@equivShrink.{u} (sheafSpacePair F T.unop) (h T.unop)).symm p).1 :=
  rfl

/-- The projection `sheafSpace.homOfPair p ⟶ Y` recovers the first component of the pair. -/
theorem sheafSpace.homOfPair_comp_sheafSpaceTo
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F)
    {T : Over S} (p : sheafSpacePair F T) :
    sheafSpace.homOfPair F h p ≫ sheafSpaceTo F h = p.1 :=
  sorry

/-- The structure morphism of the algebraic space associated to `F` is étale. -/
instance instEtale_sheafSpaceTo (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (h : IsEtaleSheafSmall F) : Etale (sheafSpaceTo F h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
