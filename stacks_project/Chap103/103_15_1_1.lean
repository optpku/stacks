module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap103.«103_15_1_1_Map»
public import stacks_project.Chap103.«103_15_1_1_FibreProduct»

/-!
# Pushforward of sheaves along restricted lisse-étale and flat-fppf functors

The identification `f'_* H(y) = Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` for a sheaf `H`
on the lisse-étale (resp. flat-fppf) site, as a Type-valued isomorphism between
cocontinuous sheaf pushforward and the limit of the pulled-back sheaf on the
primed Yoneda 2-fibre product.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open CategoryTheory CategoryTheory.ObjectProperty Functor Limits Opposite
open FiberedCategoryOver.Groupoids BasedCategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The unique vertical cartesian comparison in `Y` between `f(x)` and the chosen
pullback of `y` along a structured arrow `f'(x) ⟶ y`. -/
def lisseYonedaFibreProduct.structuredArrowCartesianIso (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) (s : StructuredArrow (op y) (lisseEtaleMap f).op) :=
  let φ0 := (lisseEtaleInclusion Y).map s.hom.unop
  let u := Y.p.map φ0
  let yFiber : Y.p.Fiber (Y.p.obj y.obj) := ⟨y.obj, rfl⟩
  let pb := IsPreFibered.pullbackMap yFiber.property u
  @IsCartesian.domainUniqueUpToIso _ _ _ _ Y.p _ _ _ _ u pb
    (IsPreFibered.pullbackMap.IsCartesian yFiber.property u) _ φ0
    (@IsFibered.InGroupoids.all_isCartesian _ _ _ _ Y.p _ _ _ φ0)

/-- The unique vertical cartesian comparison in `Y` between `f(x)` and the chosen
pullback of `y` along a structured arrow on the flat-fppf site. -/
def flatYonedaFibreProduct.structuredArrowCartesianIso (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) (s : StructuredArrow (op y) (flatFppfMap f).op) :=
  let φ0 := (flatFppfInclusion Y).map s.hom.unop
  let u := Y.p.map φ0
  let yFiber : Y.p.Fiber (Y.p.obj y.obj) := ⟨y.obj, rfl⟩
  let pb := IsPreFibered.pullbackMap yFiber.property u
  @IsCartesian.domainUniqueUpToIso _ _ _ _ Y.p _ _ _ _ u pb
    (IsPreFibered.pullbackMap.IsCartesian yFiber.property u) _ φ0
    (@IsFibered.InGroupoids.all_isCartesian _ _ _ _ Y.p _ _ _ φ0)

/-- The primed 2-fibre-product object determined by a structured arrow
`f'(x) ⟶ y`. The second projection is the source object `x`, and the fibre
comparison is the unique vertical isomorphism between `f(x)` and the chosen
cartesian pullback of `y` along the base of that arrow. -/
def lisseYonedaFibreProduct.ofStructuredArrowObj (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) (s : StructuredArrow (op y) (lisseEtaleMap f).op) :
    lisseYonedaFibreProduct f y :=
  let xObj := s.right.unop.obj
  let φ0 := (lisseEtaleInclusion Y).map s.hom.unop
  let U := Y.p.obj ((toFunctor f).obj xObj)
  let u := Y.p.map φ0
  let yFiber : Y.p.Fiber (Y.p.obj y.obj) := ⟨y.obj, rfl⟩
  let e := lisseYonedaFibreProduct.structuredArrowCartesianIso f y s
  ⟨PseudoPullback.mk
      (toBasedFunctor (YonedaSlice.representative yFiber))
      (toBasedFunctor f) U
      { fst := ⟨Over.mk u, rfl⟩
        snd :=
          ⟨xObj, congrFun (congrArg Functor.obj (toBasedFunctor f).w.symm) xObj⟩
        iso := Iso.mk ⟨e.inv, sorry⟩ ⟨e.hom, sorry⟩ sorry sorry },
    s.right.unop.property⟩

/-- The primed 2-fibre-product object determined by a structured arrow
`f'(x) ⟶ y` on the flat-fppf site. -/
def flatYonedaFibreProduct.ofStructuredArrowObj (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) (s : StructuredArrow (op y) (flatFppfMap f).op) :
    flatYonedaFibreProduct f y :=
  let xObj := s.right.unop.obj
  let φ0 := (flatFppfInclusion Y).map s.hom.unop
  let U := Y.p.obj ((toFunctor f).obj xObj)
  let u := Y.p.map φ0
  let yFiber : Y.p.Fiber (Y.p.obj y.obj) := ⟨y.obj, rfl⟩
  let e := flatYonedaFibreProduct.structuredArrowCartesianIso f y s
  ⟨PseudoPullback.mk
      (toBasedFunctor (YonedaSlice.representative yFiber))
      (toBasedFunctor f) U
      { fst := ⟨Over.mk u, rfl⟩
        snd :=
          ⟨xObj, congrFun (congrArg Functor.obj (toBasedFunctor f).w.symm) xObj⟩
        iso := Iso.mk ⟨e.inv, sorry⟩ ⟨e.hom, sorry⟩ sorry sorry },
    s.right.unop.property⟩

/-- The primed 2-fibre-product morphism associated to a morphism of structured
arrows `f'(x) ⟶ f'(x')` over `y`. The second leg is the underlying map of `X`,
and the first leg is the induced map of slice objects. -/
def lisseYonedaFibreProduct.ofStructuredArrowMap (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y)
    {s s' : StructuredArrow (op y) (lisseEtaleMap f).op} (ψ : s ⟶ s') :
    lisseYonedaFibreProduct.ofStructuredArrowObj f y s' ⟶
      lisseYonedaFibreProduct.ofStructuredArrowObj f y s :=
  let sndMap := (lisseEtaleInclusion X).map ψ.right.unop
  let baseMap := Y.p.map ((toFunctor f).map sndMap)
  ObjectProperty.homMk
    (PseudoPullback.Hom.mk
      baseMap (Over.homMk baseMap sorry) sorry sndMap sorry sorry)

/-- The primed 2-fibre-product morphism associated to a morphism of structured
arrows on the flat-fppf site. -/
def flatYonedaFibreProduct.ofStructuredArrowMap (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y)
    {s s' : StructuredArrow (op y) (flatFppfMap f).op} (ψ : s ⟶ s') :
    flatYonedaFibreProduct.ofStructuredArrowObj f y s' ⟶
      flatYonedaFibreProduct.ofStructuredArrowObj f y s :=
  let sndMap := (flatFppfInclusion X).map ψ.right.unop
  let baseMap := Y.p.map ((toFunctor f).map sndMap)
  ObjectProperty.homMk
    (PseudoPullback.Hom.mk
      baseMap (Over.homMk baseMap sorry) sorry sndMap sorry sorry)

/-- The functor sending a structured arrow `f'(x) ⟶ y` to the corresponding
object of `(V ×_{y,Y} X)'`. This is a quasi-inverse of `toStructuredArrow`. -/
def lisseYonedaFibreProduct.ofStructuredArrow (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) :
    StructuredArrow (op y) (lisseEtaleMap f).op ⥤
      (lisseYonedaFibreProduct f y)ᵒᵖ where
  obj s := op (lisseYonedaFibreProduct.ofStructuredArrowObj f y s)
  map ψ := (lisseYonedaFibreProduct.ofStructuredArrowMap f y ψ).op
  map_id := sorry
  map_comp := sorry

/-- The functor sending a structured arrow `f'(x) ⟶ y` to the corresponding
object of the flat primed 2-fibre product. -/
def flatYonedaFibreProduct.ofStructuredArrow (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) :
    StructuredArrow (op y) (flatFppfMap f).op ⥤
      (flatYonedaFibreProduct f y)ᵒᵖ where
  obj s := op (flatYonedaFibreProduct.ofStructuredArrowObj f y s)
  map ψ := (flatYonedaFibreProduct.ofStructuredArrowMap f y ψ).op
  map_id := sorry
  map_comp := sorry

/-- Identity-leg cartesian comparison from the reconstructed primed object of
`toStructuredArrow q` back to `q`. The legs are the identity on the `X`-projection
(via `pr_comp_ι`) and the induced identity-on-left slice map; the fibre
comparison is `structuredArrowCartesianIso`. -/
def lisseYonedaFibreProduct.ofToStructuredArrowIso (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) (q : (lisseYonedaFibreProduct f y)ᵒᵖ) :
    lisseYonedaFibreProduct.ofStructuredArrowObj f y
        ((lisseYonedaFibreProduct.toStructuredArrow f y).obj q) ≅ q.unop :=
  let recon :=
    lisseYonedaFibreProduct.ofStructuredArrowObj f y
      ((lisseYonedaFibreProduct.toStructuredArrow f y).obj q)
  let e :=
    lisseYonedaFibreProduct.structuredArrowCartesianIso f y
      ((lisseYonedaFibreProduct.toStructuredArrow f y).obj q)
  let baseMap :=
    (PseudoPullback.sndBaseIso recon.obj).inv ≫
      (PseudoPullback.sndBaseIso q.unop.obj).hom
  let baseMapInv :=
    (PseudoPullback.sndBaseIso q.unop.obj).inv ≫
      (PseudoPullback.sndBaseIso recon.obj).hom
  Iso.mk
    (ObjectProperty.homMk
      (PseudoPullback.Hom.mk baseMap
        (Over.homMk
          ((PseudoPullback.fstBaseIso recon.obj).hom ≫ baseMap ≫
            (PseudoPullback.fstBaseIso q.unop.obj).inv)
          sorry)
        sorry ((lisseYonedaFibreProduct.pr_comp_ι f y).hom.app q.unop) sorry sorry))
    (ObjectProperty.homMk
      (PseudoPullback.Hom.mk baseMapInv
        (Over.homMk
          ((PseudoPullback.fstBaseIso q.unop.obj).hom ≫ baseMapInv ≫
            (PseudoPullback.fstBaseIso recon.obj).inv)
          sorry)
        sorry ((lisseYonedaFibreProduct.pr_comp_ι f y).inv.app q.unop) sorry sorry))
    sorry sorry

/-- Identity-leg cartesian comparison from the reconstructed flat primed object
of `toStructuredArrow q` back to `q`. -/
def flatYonedaFibreProduct.ofToStructuredArrowIso (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) (q : (flatYonedaFibreProduct f y)ᵒᵖ) :
    flatYonedaFibreProduct.ofStructuredArrowObj f y
        ((flatYonedaFibreProduct.toStructuredArrow f y).obj q) ≅ q.unop :=
  let recon :=
    flatYonedaFibreProduct.ofStructuredArrowObj f y
      ((flatYonedaFibreProduct.toStructuredArrow f y).obj q)
  let e :=
    flatYonedaFibreProduct.structuredArrowCartesianIso f y
      ((flatYonedaFibreProduct.toStructuredArrow f y).obj q)
  let baseMap :=
    (PseudoPullback.sndBaseIso recon.obj).inv ≫
      (PseudoPullback.sndBaseIso q.unop.obj).hom
  let baseMapInv :=
    (PseudoPullback.sndBaseIso q.unop.obj).inv ≫
      (PseudoPullback.sndBaseIso recon.obj).hom
  Iso.mk
    (ObjectProperty.homMk
      (PseudoPullback.Hom.mk baseMap
        (Over.homMk
          ((PseudoPullback.fstBaseIso recon.obj).hom ≫ baseMap ≫
            (PseudoPullback.fstBaseIso q.unop.obj).inv)
          sorry)
        sorry ((flatYonedaFibreProduct.pr_comp_ι f y).hom.app q.unop) sorry sorry))
    (ObjectProperty.homMk
      (PseudoPullback.Hom.mk baseMapInv
        (Over.homMk
          ((PseudoPullback.fstBaseIso q.unop.obj).hom ≫ baseMapInv ≫
            (PseudoPullback.fstBaseIso recon.obj).inv)
          sorry)
        sorry ((flatYonedaFibreProduct.pr_comp_ι f y).inv.app q.unop) sorry sorry))
    sorry sorry

/-- The counit isomorphism `toStructuredArrow (ofStructuredArrow s) ≅ s`, with
identity right leg. The commuting triangle is the cartesian comparison
`structuredArrowCartesianIso`. -/
def lisseYonedaFibreProduct.toOfStructuredArrowIso (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) (s : StructuredArrow (op y) (lisseEtaleMap f).op) :
    (lisseYonedaFibreProduct.toStructuredArrow f y).obj
        ((lisseYonedaFibreProduct.ofStructuredArrow f y).obj s) ≅ s :=
  let e := lisseYonedaFibreProduct.structuredArrowCartesianIso f y s
  Iso.mk (StructuredArrow.homMk (𝟙 s.right) sorry)
    (StructuredArrow.homMk (𝟙 s.right) sorry) sorry sorry

/-- The counit isomorphism `toStructuredArrow (ofStructuredArrow s) ≅ s` on the
flat-fppf site. -/
def flatYonedaFibreProduct.toOfStructuredArrowIso (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) (s : StructuredArrow (op y) (flatFppfMap f).op) :
    (flatYonedaFibreProduct.toStructuredArrow f y).obj
        ((flatYonedaFibreProduct.ofStructuredArrow f y).obj s) ≅ s :=
  let e := flatYonedaFibreProduct.structuredArrowCartesianIso f y s
  Iso.mk (StructuredArrow.homMk (𝟙 s.right) sorry)
    (StructuredArrow.homMk (𝟙 s.right) sorry) sorry sorry

/-- Unit of the quasi-inverse: `toStructuredArrow ⋙ ofStructuredArrow ≅ 𝟭`
on `(V ×_{y,Y} X)'ᵒᵖ`. -/
def lisseYonedaFibreProduct.unitIso (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    𝟭 (lisseYonedaFibreProduct f y)ᵒᵖ ≅
      lisseYonedaFibreProduct.toStructuredArrow f y ⋙
        lisseYonedaFibreProduct.ofStructuredArrow f y :=
  NatIso.ofComponents
    (fun q ↦ (lisseYonedaFibreProduct.ofToStructuredArrowIso f y q).op) sorry

/-- Unit of the quasi-inverse on the flat primed 2-fibre product. -/
def flatYonedaFibreProduct.unitIso (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    𝟭 (flatYonedaFibreProduct f y)ᵒᵖ ≅
      flatYonedaFibreProduct.toStructuredArrow f y ⋙
        flatYonedaFibreProduct.ofStructuredArrow f y :=
  NatIso.ofComponents
    (fun q ↦ (flatYonedaFibreProduct.ofToStructuredArrowIso f y q).op) sorry

/-- Counit of the quasi-inverse: `ofStructuredArrow ⋙ toStructuredArrow ≅ 𝟭`
on the comma category of arrows `f'(x) ⟶ y`. -/
def lisseYonedaFibreProduct.counitIso (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y) :
    lisseYonedaFibreProduct.ofStructuredArrow f y ⋙
        lisseYonedaFibreProduct.toStructuredArrow f y ≅
      𝟭 (StructuredArrow (op y) (lisseEtaleMap f).op) :=
  NatIso.ofComponents (fun s ↦ lisseYonedaFibreProduct.toOfStructuredArrowIso f y s)
    sorry

/-- Counit of the quasi-inverse on the flat-fppf comma category. -/
def flatYonedaFibreProduct.counitIso (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y) :
    flatYonedaFibreProduct.ofStructuredArrow f y ⋙
        flatYonedaFibreProduct.toStructuredArrow f y ≅
      𝟭 (StructuredArrow (op y) (flatFppfMap f).op) :=
  NatIso.ofComponents (fun s ↦ flatYonedaFibreProduct.toOfStructuredArrowIso f y s)
    sorry

/-- The unit and counit of `toStructuredArrow` and `ofStructuredArrow` satisfy
the triangle identity on the comma category. -/
theorem lisseYonedaFibreProduct.toStructuredArrow_ofStructuredArrow_triangle
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (q : (lisseYonedaFibreProduct f y)ᵒᵖ) :
    (lisseYonedaFibreProduct.toStructuredArrow f y).map
          ((lisseYonedaFibreProduct.unitIso f y).hom.app q) ≫
        (lisseYonedaFibreProduct.counitIso f y).hom.app
          ((lisseYonedaFibreProduct.toStructuredArrow f y).obj q) =
      𝟙 ((lisseYonedaFibreProduct.toStructuredArrow f y).obj q) :=
  sorry

/-- The unit and counit of the flat `toStructuredArrow` and `ofStructuredArrow`
satisfy the triangle identity on the comma category. -/
theorem flatYonedaFibreProduct.toStructuredArrow_ofStructuredArrow_triangle
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (q : (flatYonedaFibreProduct f y)ᵒᵖ) :
    (flatYonedaFibreProduct.toStructuredArrow f y).map
          ((flatYonedaFibreProduct.unitIso f y).hom.app q) ≫
        (flatYonedaFibreProduct.counitIso f y).hom.app
          ((flatYonedaFibreProduct.toStructuredArrow f y).obj q) =
      𝟙 ((flatYonedaFibreProduct.toStructuredArrow f y).obj q) :=
  sorry

/-- The unit and counit of `toStructuredArrow` and `ofStructuredArrow` satisfy
the triangle identity on `(V ×_{y,Y} X)'ᵒᵖ`. -/
theorem lisseYonedaFibreProduct.ofStructuredArrow_toStructuredArrow_triangle
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (s : StructuredArrow (op y) (lisseEtaleMap f).op) :
    (lisseYonedaFibreProduct.unitIso f y).hom.app
          ((lisseYonedaFibreProduct.ofStructuredArrow f y).obj s) ≫
        (lisseYonedaFibreProduct.ofStructuredArrow f y).map
          ((lisseYonedaFibreProduct.counitIso f y).hom.app s) =
      𝟙 ((lisseYonedaFibreProduct.ofStructuredArrow f y).obj s) :=
  sorry

/-- The unit and counit of the flat `toStructuredArrow` and `ofStructuredArrow`
satisfy the triangle identity on the primed 2-fibre product. -/
theorem flatYonedaFibreProduct.ofStructuredArrow_toStructuredArrow_triangle
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (s : StructuredArrow (op y) (flatFppfMap f).op) :
    (flatYonedaFibreProduct.unitIso f y).hom.app
          ((flatYonedaFibreProduct.ofStructuredArrow f y).obj s) ≫
        (flatYonedaFibreProduct.ofStructuredArrow f y).map
          ((flatYonedaFibreProduct.counitIso f y).hom.app s) =
      𝟙 ((flatYonedaFibreProduct.ofStructuredArrow f y).obj s) :=
  sorry

/-- Reindexing the comma-limit diagram along `ofStructuredArrow` does not change
the existence of its limit. -/
instance lisseYonedaFibreProduct.hasLimit_ofStructuredArrow_comp
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1)))
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P] :
    HasLimit
      (lisseYonedaFibreProduct.ofStructuredArrow f y ⋙
        lisseYonedaFibreProduct.toStructuredArrow f y ⋙
          StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) :=
  hasLimit_of_iso
    ((Functor.leftUnitor
          (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)).symm ≪≫
      isoWhiskerRight (lisseYonedaFibreProduct.counitIso f y).symm
        (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) ≪≫
      Functor.associator (lisseYonedaFibreProduct.ofStructuredArrow f y)
        (lisseYonedaFibreProduct.toStructuredArrow f y)
        (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj))

/-- Reindexing the flat comma-limit diagram along `ofStructuredArrow` does not
change the existence of its limit. -/
instance flatYonedaFibreProduct.hasLimit_ofStructuredArrow_comp
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (H : Sheaf (flatFppfTopology X) (Type (u + 1)))
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P] :
    HasLimit
      (flatYonedaFibreProduct.ofStructuredArrow f y ⋙
        flatYonedaFibreProduct.toStructuredArrow f y ⋙
          StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) :=
  hasLimit_of_iso
    ((Functor.leftUnitor
          (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)).symm ≪≫
      isoWhiskerRight (flatYonedaFibreProduct.counitIso f y).symm
        (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) ≪≫
      Functor.associator (flatYonedaFibreProduct.ofStructuredArrow f y)
        (flatYonedaFibreProduct.toStructuredArrow f y)
        (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj))

/-- The forward map of the identification
`f'_* H(y) ⟶ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the lisse-étale site, obtained by
evaluating the pointwise right Kan extension as a comma limit and reindexing
along `lisseYonedaFibreProduct.toStructuredArrow`. -/
def lisseEtalePushforwardObjIsoGlobalSectionsHom (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) ⟶
      limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  ((lisseEtaleMap f).op.ranObjObjIsoLimit H.obj (op y)).hom ≫
    limit.pre (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)
      (lisseYonedaFibreProduct.toStructuredArrow f y) ≫
    (HasLimit.isoOfNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
          (lisseYonedaFibreProduct.toStructuredArrow f y ⋙
              StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) ≅
            (lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)).hom

/-- The reverse map of the identification
`Γ((V ×_{y,Y} X)', (pr')⁻¹ H) ⟶ f'_* H(y)` on the lisse-étale site, obtained by
reindexing the primed-limit along `ofStructuredArrow`, conjugating by the
counit `toStructuredArrow ∘ ofStructuredArrow ≅ 𝟭` and the componentwise
`Iso.refl` reindex, and inverting the pointwise right Kan extension
evaluation. -/
def lisseEtalePushforwardObjIsoGlobalSectionsInv (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) ⟶
      (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
          (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) :=
  (HasLimit.isoOfNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
          (lisseYonedaFibreProduct.toStructuredArrow f y ⋙
              StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) ≅
            (lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)).inv ≫
    limit.pre
      (lisseYonedaFibreProduct.toStructuredArrow f y ⋙
        StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)
      (lisseYonedaFibreProduct.ofStructuredArrow f y) ≫
    (HasLimit.isoOfNatIso
        ((Functor.associator (lisseYonedaFibreProduct.ofStructuredArrow f y)
              (lisseYonedaFibreProduct.toStructuredArrow f y)
              (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)).symm ≪≫
          isoWhiskerRight (lisseYonedaFibreProduct.counitIso f y)
            (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) ≪≫
          Functor.leftUnitor
            (StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj))).hom ≫
    ((lisseEtaleMap f).op.ranObjObjIsoLimit H.obj (op y)).inv

/-- 103.15.1.1 (1): if `f : X ⟶ Y` is a smooth morphism of algebraic stacks,
then `f` restricts to a continuous cocontinuous functor
`f' = lisseEtaleMap f` of lisse-étale sites. For a sheaf `H` on
`X_{lisse,étale}` and an object `y` of `Y_{lisse,étale}` over a scheme `V`,
there is a canonical identification
`f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)`, where `(V ×_{y,Y} X)'` is the
full subcategory `lisseYonedaFibreProduct f y` of the Yoneda 2-fibre product
on objects whose induced map to `X` is smooth, and `pr'` is the restricted
projection to `X_{lisse,étale}`. Pushforward is
`(lisseEtaleMap f).sheafPushforwardCocontinuous`, `(pr')⁻¹` is precomposition
with `(lisseYonedaFibreProduct.pr f y).op`, and `Γ` of a Type-valued sheaf is
the limit. -/
@[stacks 07AU]
def lisseEtalePushforwardObjIsoGlobalSections (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.obj (op y) ≅
      limit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  Iso.mk (lisseEtalePushforwardObjIsoGlobalSectionsHom f H y)
    (lisseEtalePushforwardObjIsoGlobalSectionsInv f H y) sorry sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` computes on
an object `q` of the primed 2-fibre product as the limit projection of
`(pr')⁻¹ H` at `pr'(q)`. -/
theorem lisseEtalePushforwardObjIsoGlobalSections_π (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1))) (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    (q : lisseYonedaFibreProduct f y) :
    (lisseEtalePushforwardObjIsoGlobalSections f H y).hom ≫
        limit.π ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) (op q) =
      (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj H).obj.map
          (op (lisseYonedaFibreProduct.arrow f y q)) ≫
        ((lisseEtaleMap f).op.ranCounit.app H.obj).app
          (op ((lisseYonedaFibreProduct.pr f y).obj q)) :=
  sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` is natural in
the sheaf `H`. -/
theorem lisseEtalePushforwardObjIsoGlobalSections_natural (f : X ⟶ Y) [Smooth f]
    {H G : Sheaf (lisseEtaleTopology X) (Type (u + 1))} (τ : H ⟶ G)
    (y : lisseEtaleSite Y)
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ G.obj)] :
    (lisseEtalePushforwardObjIsoGlobalSections f H y).hom ≫
        limMap (whiskerLeft (lisseYonedaFibreProduct.pr f y).op
          ((sheafToPresheaf (lisseEtaleTopology X) (Type (u + 1))).map τ)) =
      (((lisseEtaleMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (lisseEtaleTopology X) (lisseEtaleTopology Y)).map τ).hom.app (op y) ≫
        (lisseEtalePushforwardObjIsoGlobalSections f G y).hom :=
  sorry

/-- The forward map of the identification
`f'_* H(y) ⟶ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the flat-fppf site. -/
def flatFppfPushforwardObjIsoGlobalSectionsHom (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) ⟶
      limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  ((flatFppfMap f).op.ranObjObjIsoLimit H.obj (op y)).hom ≫
    limit.pre (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)
      (flatYonedaFibreProduct.toStructuredArrow f y) ≫
    (HasLimit.isoOfNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
          (flatYonedaFibreProduct.toStructuredArrow f y ⋙
              StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) ≅
            (flatYonedaFibreProduct.pr f y).op ⋙ H.obj)).hom

/-- The reverse map of the identification
`Γ((V ×_{y,Y} X)', (pr')⁻¹ H) ⟶ f'_* H(y)` on the flat-fppf site, obtained by
reindexing the primed-limit along `ofStructuredArrow`, conjugating by the
counit `toStructuredArrow ∘ ofStructuredArrow ≅ 𝟭` and the componentwise
`Iso.refl` reindex, and inverting the pointwise right Kan extension
evaluation. -/
def flatFppfPushforwardObjIsoGlobalSectionsInv (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) ⟶
      (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
          (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) :=
  (HasLimit.isoOfNatIso
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
          (flatYonedaFibreProduct.toStructuredArrow f y ⋙
              StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) ≅
            (flatYonedaFibreProduct.pr f y).op ⋙ H.obj)).inv ≫
    limit.pre
      (flatYonedaFibreProduct.toStructuredArrow f y ⋙
        StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)
      (flatYonedaFibreProduct.ofStructuredArrow f y) ≫
    (HasLimit.isoOfNatIso
        ((Functor.associator (flatYonedaFibreProduct.ofStructuredArrow f y)
              (flatYonedaFibreProduct.toStructuredArrow f y)
              (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)).symm ≪≫
          isoWhiskerRight (flatYonedaFibreProduct.counitIso f y)
            (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) ≪≫
          Functor.leftUnitor
            (StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj))).hom ≫
    ((flatFppfMap f).op.ranObjObjIsoLimit H.obj (op y)).inv

/-- 103.15.1.1 (2): if `f : X ⟶ Y` is a flat morphism of algebraic stacks, then
`f` restricts to a continuous cocontinuous functor `f' = flatFppfMap f` of
flat-fppf sites. For a sheaf `H` on `X_{flat,fppf}` and an object `y` of
`Y_{flat,fppf}` over a scheme `V`, there is a canonical identification
`f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)`, where `(V ×_{y,Y} X)'` is the
full subcategory `flatYonedaFibreProduct f y` of the Yoneda 2-fibre product on
objects whose induced map to `X` is flat, and `pr'` is the restricted
projection to `X_{flat,fppf}`. -/
@[stacks 07AU]
def flatFppfPushforwardObjIsoGlobalSections (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
        (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.obj (op y) ≅
      limit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) :=
  Iso.mk (flatFppfPushforwardObjIsoGlobalSectionsHom f H y)
    (flatFppfPushforwardObjIsoGlobalSectionsInv f H y) sorry sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the
flat-fppf site computes on an object `q` of the primed 2-fibre product as the
limit projection of `(pr')⁻¹ H` at `pr'(q)`. -/
theorem flatFppfPushforwardObjIsoGlobalSections_π (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) (Type (u + 1))) (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    (q : flatYonedaFibreProduct f y) :
    (flatFppfPushforwardObjIsoGlobalSections f H y).hom ≫
        limit.π ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) (op q) =
      (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (flatFppfTopology X) (flatFppfTopology Y)).obj H).obj.map
          (op (flatYonedaFibreProduct.arrow f y q)) ≫
        ((flatFppfMap f).op.ranCounit.app H.obj).app
          (op ((flatYonedaFibreProduct.pr f y).obj q)) :=
  sorry

/-- The identification `f'_* H(y) ≅ Γ((V ×_{y,Y} X)', (pr')⁻¹ H)` on the
flat-fppf site is natural in the sheaf `H`. -/
theorem flatFppfPushforwardObjIsoGlobalSections_natural (f : X ⟶ Y) [Flat f]
    {H G : Sheaf (flatFppfTopology X) (Type (u + 1))} (τ : H ⟶ G)
    (y : flatFppfSite Y)
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type (u + 1),
      (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)]
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ G.obj)] :
    (flatFppfPushforwardObjIsoGlobalSections f H y).hom ≫
        limMap (whiskerLeft (flatYonedaFibreProduct.pr f y).op
          ((sheafToPresheaf (flatFppfTopology X) (Type (u + 1))).map τ)) =
      (((flatFppfMap f).sheafPushforwardCocontinuous (Type (u + 1))
            (flatFppfTopology X) (flatFppfTopology Y)).map τ).hom.app (op y) ≫
        (flatFppfPushforwardObjIsoGlobalSections f G y).hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
