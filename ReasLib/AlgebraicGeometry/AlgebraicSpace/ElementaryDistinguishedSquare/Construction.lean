module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.Quot
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare.Relation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Sheafification

/-!
# Pushout algebraic space of a separated étale open span

The quotient `W = (U ⊔ V) / R` of the five-summand étale equivalence
relation is an algebraic space over `S`, and supplies the
canonical maps of the pushout of an open immersion along a separated étale
morphism. The objectwise quotient is kept as a Type `u` presheaf; `W` is the
Type `u` quotient obtained on the certified small étale sites of test schemes.
The étale equivalence relation makes this quotient an fppf sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

variable {S : Scheme.{u}}

/-- A `T`-point of the pointwise coproduct of `U` and `V`. -/
abbrev uvPoint (U V : AlgebraicSpace S) (T : Over S) : Type u :=
  U.functorOfPoints.obj (op T) ⊕ V.functorOfPoints.obj (op T)

/-- Restriction of a pointwise coproduct section along a morphism of schemes over `S`. -/
def uvPointMap {U V : AlgebraicSpace S} {T T' : Over S} (g : T' ⟶ T) :
    uvPoint U V T → uvPoint U V T' :=
  Sum.map (fun u ↦ U.functorOfPoints.map g.op u) (fun v ↦ V.functorOfPoints.map g.op v)

/-- Restriction of pointwise coproduct sections is functorial in the test scheme. -/
theorem uvPointMap_comp {U V : AlgebraicSpace S} {T T' T'' : Over S}
    (g : T' ⟶ T) (f : T'' ⟶ T') (x : uvPoint U V T) :
    uvPointMap f (uvPointMap g x) = uvPointMap (f ≫ g) x :=
  match x with
  | Sum.inl u =>
      congrArg Sum.inl <|
        (CategoryTheory.comp_apply (U.functorOfPoints.map g.op)
            (U.functorOfPoints.map f.op) u).symm.trans <|
          congrArg (fun φ ↦ φ u) (U.functorOfPoints.map_comp g.op f.op).symm
  | Sum.inr v =>
      congrArg Sum.inr <|
        (CategoryTheory.comp_apply (V.functorOfPoints.map g.op)
            (V.functorOfPoints.map f.op) v).symm.trans <|
          congrArg (fun φ ↦ φ v) (V.functorOfPoints.map_comp g.op f.op).symm

/-- The generating relation of `R` on pointwise `(U ⊔ V)`-points: the five pair maps
from `U`, `V'`, `V'`, `V`, and the off-diagonal complement of `Δ_{V'/U}`. -/
def glueRel {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U) [Separated f']
    (T : Over S) : uvPoint U V T → uvPoint U V T → Prop :=
  fun x y ↦
    (∃ u : U.functorOfPoints.obj (op T), x = Sum.inl u ∧ y = Sum.inl u) ∨
      (∃ v : V.functorOfPoints.obj (op T), x = Sum.inr v ∧ y = Sum.inr v) ∨
        (∃ v' : V'.functorOfPoints.obj (op T),
          x = Sum.inl (f'.app (op T) v') ∧ y = Sum.inr (ι.app (op T) v')) ∨
          (∃ v' : V'.functorOfPoints.obj (op T),
            x = Sum.inr (ι.app (op T) v') ∧ y = Sum.inl (f'.app (op T) v')) ∨
            ∃ w : (offDiagonal f').functorOfPoints.obj (op T),
              x = Sum.inr ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T) w) ∧
                y = Sum.inr ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T) w)

/-- Two pointwise coproduct points are related exactly by the five generating pair maps. -/
theorem glueRel_iff {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : Over S) (x y : uvPoint U V T) :
    glueRel ι f' T x y ↔
      (∃ u : U.functorOfPoints.obj (op T), x = Sum.inl u ∧ y = Sum.inl u) ∨
        (∃ v : V.functorOfPoints.obj (op T), x = Sum.inr v ∧ y = Sum.inr v) ∨
          (∃ v' : V'.functorOfPoints.obj (op T),
            x = Sum.inl (f'.app (op T) v') ∧ y = Sum.inr (ι.app (op T) v')) ∨
            (∃ v' : V'.functorOfPoints.obj (op T),
              x = Sum.inr (ι.app (op T) v') ∧ y = Sum.inl (f'.app (op T) v')) ∨
              ∃ w : (offDiagonal f').functorOfPoints.obj (op T),
                x = Sum.inr ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T) w) ∧
                  y = Sum.inr ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T) w) :=
  Iff.rfl

/-- Restriction of schemes over `S` preserves the generating image of `R`. -/
theorem glueRel_precomp {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {T T' : Over S} (g : T' ⟶ T) {x y : uvPoint U V T}
    (h : glueRel ι f' T x y) :
    glueRel ι f' T' (uvPointMap g x) (uvPointMap g y) :=
  match h with
  | Or.inl ⟨u, hx, hy⟩ =>
      Or.inl ⟨U.functorOfPoints.map g.op u,
        congrArg (uvPointMap g) hx, congrArg (uvPointMap g) hy⟩
  | Or.inr (Or.inl ⟨v, hx, hy⟩) =>
      Or.inr <| Or.inl ⟨V.functorOfPoints.map g.op v,
        congrArg (uvPointMap g) hx, congrArg (uvPointMap g) hy⟩
  | Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩)) =>
      Or.inr <| Or.inr <| Or.inl ⟨V'.functorOfPoints.map g.op v',
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inl (NatTrans.naturality_apply f' g.op v').symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inr (NatTrans.naturality_apply ι g.op v').symm)⟩
  | Or.inr (Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩))) =>
      Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨V'.functorOfPoints.map g.op v',
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inr (NatTrans.naturality_apply ι g.op v').symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inl (NatTrans.naturality_apply f' g.op v').symm)⟩
  | Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hx, hy⟩))) =>
      Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨(offDiagonal f').functorOfPoints.map g.op w,
        (congrArg (uvPointMap g) hx).trans
          (congrArg Sum.inr
            (NatTrans.naturality_apply (offDiagonalι f' ≫ pullback.fst f' f' ≫ ι) g.op w).symm),
        (congrArg (uvPointMap g) hy).trans
          (congrArg Sum.inr
            (NatTrans.naturality_apply (offDiagonalι f' ≫ pullback.snd f' f' ≫ ι) g.op w).symm)⟩

/-- Evaluate a compatible pair of maps `U ⟶ B` and `V ⟶ B` on a pointwise coproduct section. -/
def uvHomApp {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B) {T : Over S} :
    uvPoint U V T → B.functorOfPoints.obj (op T) :=
  Sum.elim (fun u ↦ hU.app (op T) u) (fun v ↦ hV.app (op T) v)

/-- The evaluation map `uvHomApp` is natural in the test scheme. -/
theorem uvHomApp_natural {U V B : AlgebraicSpace S} (hU : U ⟶ B) (hV : V ⟶ B)
    {T T' : Over S} (g : T' ⟶ T) (x : uvPoint U V T) :
    B.functorOfPoints.map g.op (uvHomApp hU hV x) = uvHomApp hU hV (uvPointMap g x) :=
  match x with
  | Sum.inl u => (NatTrans.naturality_apply hU g.op u).symm
  | Sum.inr v => (NatTrans.naturality_apply hV g.op v).symm

/-- The two off-diagonal legs become equal after composing with a compatible pair of maps. -/
private theorem offDiag_comp_eq {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) :
    offDiagonalι f' ≫ pullback.fst f' f' ≫ ι ≫ hV =
      offDiagonalι f' ≫ pullback.snd f' f' ≫ ι ≫ hV :=
  congrArg (fun k ↦ offDiagonalι f' ≫ k) <|
    (congrArg (fun k ↦ pullback.fst f' f' ≫ k) h).trans <|
      (Category.assoc (pullback.fst f' f') f' hU).symm.trans <|
        (congrArg (fun k ↦ k ≫ hU) pullback.condition).trans <|
          (Category.assoc (pullback.snd f' f') f' hU).trans <|
            congrArg (fun k ↦ pullback.snd f' f' ≫ k) h.symm

/-- Related points of `U ⊔ V` have the same image under a compatible pair of maps into an
algebraic space `B`. -/
theorem glueRel_hom_eq {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) {T : Over S}
    {x y : uvPoint U V T} (hxy : glueRel ι f' T x y) :
    uvHomApp hU hV x = uvHomApp hU hV y :=
  match hxy with
  | Or.inl ⟨_, hx, hy⟩ => (congrArg (uvHomApp hU hV) hx).trans (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inl ⟨_, hx, hy⟩) =>
      (congrArg (uvHomApp hU hV) hx).trans (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩)) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply (f'.app (op T)) (hU.app (op T)) v').symm.trans <|
            (ConcreteCategory.congr_hom (NatTrans.congr_app h.symm (op T)) v').trans <|
              CategoryTheory.comp_apply (ι.app (op T)) (hV.app (op T)) v').trans <|
          (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inr (Or.inl ⟨v', hx, hy⟩))) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply (ι.app (op T)) (hV.app (op T)) v').symm.trans <|
            (ConcreteCategory.congr_hom (NatTrans.congr_app h (op T)) v').trans <|
              CategoryTheory.comp_apply (f'.app (op T)) (hU.app (op T)) v').trans <|
          (congrArg (uvHomApp hU hV) hy).symm
  | Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hx, hy⟩))) =>
      (congrArg (uvHomApp hU hV) hx).trans <|
        ((CategoryTheory.comp_apply
              ((offDiagonalι f' ≫ pullback.fst f' f' ≫ ι).app (op T)) (hV.app (op T)) w).symm.trans <|
            (ConcreteCategory.congr_hom
                (NatTrans.congr_app (offDiag_comp_eq ι f' hV hU h) (op T)) w).trans <|
              CategoryTheory.comp_apply
                ((offDiagonalι f' ≫ pullback.snd f' f' ≫ ι).app (op T)) (hV.app (op T)) w).trans <|
          (congrArg (uvHomApp hU hV) hy).symm

/-- The quotient restriction operation preserves identity morphisms. -/
theorem gluePresheaf_map_id {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : Over S) :
    (TypeCat.ofHom (Quot.map (uvPointMap (𝟙 T))
        (fun _ _ h ↦ glueRel_precomp ι f' (𝟙 T) h)) :
      Quot (glueRel ι f' T) ⟶ Quot (glueRel ι f' T)) = 𝟙 _ := sorry

/-- The quotient restriction operation preserves composition of morphisms. -/
theorem gluePresheaf_map_comp {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f']
    {T T' T'' : Over S} (g : T' ⟶ T) (f : T'' ⟶ T') :
    (TypeCat.ofHom (Quot.map (uvPointMap (f ≫ g))
        (fun _ _ h ↦ glueRel_precomp ι f' (f ≫ g) h)) :
      Quot (glueRel ι f' T) ⟶ Quot (glueRel ι f' T'')) =
      (TypeCat.ofHom (Quot.map (uvPointMap g)
        (fun _ _ h ↦ glueRel_precomp ι f' g h)) :
      Quot (glueRel ι f' T) ⟶ Quot (glueRel ι f' T')) ≫
        (TypeCat.ofHom (Quot.map (uvPointMap f)
        (fun _ _ h ↦ glueRel_precomp ι f' f h)) :
      Quot (glueRel ι f' T') ⟶ Quot (glueRel ι f' T'')) := sorry

/-- The Type `u` presheaf sending `T` to the quotient of the pointwise coproduct
`(U ⊔ V)(T)` by the image of `R(T)`. This is not an fppf sheaf. -/
def gluePresheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Quot (glueRel ι f' T.unop)
  map {X Y} η :=
    TypeCat.ofHom <|
      Quot.map (uvPointMap η.unop) fun _ _ h ↦ glueRel_precomp ι f' η.unop h
  map_id T := gluePresheaf_map_id ι f' T.unop
  map_comp := by
    intro X Y Z g f
    exact gluePresheaf_map_comp ι f' g.unop f.unop

/-- The value of `gluePresheaf` on `T` is the objectwise quotient by `glueRel`. -/
theorem gluePresheaf_obj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : Over S) :
    (gluePresheaf ι f').obj (op T) = Quot (glueRel ι f' T) :=
  rfl

/-- Restriction in `gluePresheaf` is induced by `uvPointMap` on representatives. -/
theorem gluePresheaf_map_mk {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {T T' : Over S} (g : T' ⟶ T) (x : uvPoint U V T) :
    (gluePresheaf ι f').map g.op (Quot.mk (glueRel ι f' T) x) =
      Quot.mk (glueRel ι f' T') (uvPointMap g x) :=
  rfl

/-- Evaluating a compatible pair of maps on a `gluePresheaf` class is natural. -/
theorem gluePresheaf_hom_natural {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU)
    {T T' : Over S} (g : T' ⟶ T) (q : Quot (glueRel ι f' T)) :
    B.functorOfPoints.map g.op
        (Quot.lift (uvHomApp hU hV) (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy) q) =
      Quot.lift (uvHomApp hU hV) (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy)
        ((gluePresheaf ι f').map g.op q) :=
  Quot.inductionOn q fun x ↦ uvHomApp_natural hU hV g x

/-- Restriction in `gluePresheaf` is functorial on quotient classes. -/
theorem gluePresheaf_map_comp_apply {U V V' : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [Separated f'] {T T' T'' : Over S} (g : T' ⟶ T) (f : T'' ⟶ T')
    (q : Quot (glueRel ι f' T)) :
    (gluePresheaf ι f').map f.op ((gluePresheaf ι f').map g.op q) =
      (gluePresheaf ι f').map (f ≫ g).op q :=
  Quot.inductionOn q fun x ↦
    congrArg (Quot.mk (glueRel ι f' T'')) (uvPointMap_comp g f x)



/-- The étale sheafification of the objectwise quotient by the five-summand relation. -/
def glueSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : (Over S)ᵒᵖ ⥤ Type u :=
  Scheme.EtaleSheafification.sheafify (gluePresheaf ι f')

/-- The quotient sheaf is evaluated at the local identity section of each test scheme. -/
theorem glueSheaf_obj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (T : (Over S)ᵒᵖ) :
    (glueSheaf ι f').obj T =
      (Scheme.EtaleSheafification.localSheaf (gluePresheaf ι f') T.unop).obj.obj
        (op (Scheme.Etale.mk (𝟙 T.unop.left))) :=
  rfl

/-- Restriction in the quotient sheaf is the local small-site restriction operation. -/
theorem glueSheaf_map {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] {X Y : (Over S)ᵒᵖ} (g : X ⟶ Y) :
    (glueSheaf ι f').map g =
      Scheme.EtaleSheafification.restrictionMap (gluePresheaf ι f') g.unop :=
  rfl

/-- The étale quotient of the five-summand étale equivalence relation satisfies fppf descent. -/
theorem glueSheaf_isSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (glueSheaf ι f') :=
  sorry

/-- The sheafification unit of the objectwise quotient presheaf. -/
def toGlueSheaf {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] : gluePresheaf ι f' ⟶ glueSheaf ι f' :=
  Scheme.EtaleSheafification.toSheafify (gluePresheaf ι f')

/-- The quotient unit is locally injective for the fppf topology. -/
instance instIsLocallyInjective_toGlueSheaf {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (toGlueSheaf ι f') :=
  sorry

/-- The quotient unit is locally surjective for the fppf topology. -/
instance instIsLocallySurjective_toGlueSheaf {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (toGlueSheaf ι f') :=
  sorry

/-- The diagonal of the sheafified quotient is representable by schemes. -/
theorem glueSheaf_representableDiagonal {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    yoneda.relativelyRepresentable (Limits.diag (glueSheaf ι f')) := sorry

/-- The sheafified quotient admits a representable étale locally surjective atlas. -/
theorem glueSheaf_atlas {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    ∃ (T : Over S) (p : yoneda.obj T ⟶ glueSheaf ι f'),
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space of the fppf quotient of the specified étale relation. -/
def pushoutObj {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : AlgebraicSpace S :=
  ofFunctor (glueSheaf ι f') (glueSheaf_isSheaf ι f')
    (glueSheaf_representableDiagonal ι f') (glueSheaf_atlas ι f')

/-- The canonical V-summand map to the quotient commutes with restriction. -/
theorem inl_naturality {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f']
    {X Y : (Over S)ᵒᵖ} (g : X ⟶ Y) :
    V.functorOfPoints.map g ≫
        TypeCat.ofHom (fun v ↦ (toGlueSheaf ι f').app Y
          (Quot.mk (glueRel ι f' Y.unop) (Sum.inr v))) =
      TypeCat.ofHom (fun v ↦ (toGlueSheaf ι f').app X
        (Quot.mk (glueRel ι f' X.unop) (Sum.inr v))) ≫ (glueSheaf ι f').map g := sorry

/-- The canonical map from the V summand to the fppf quotient. -/
def inl {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : V ⟶ pushoutObj ι f' where
  app T := ↾fun v ↦ (toGlueSheaf ι f').app T
    (Quot.mk (glueRel ι f' T.unop) (Sum.inr v))
  naturality := by
    intro X Y g
    exact inl_naturality ι f' g

/-- The canonical U-summand map to the quotient commutes with restriction. -/
theorem inr_naturality {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f']
    {X Y : (Over S)ᵒᵖ} (g : X ⟶ Y) :
    U.functorOfPoints.map g ≫
        TypeCat.ofHom (fun v ↦ (toGlueSheaf ι f').app Y
          (Quot.mk (glueRel ι f' Y.unop) (Sum.inl v))) =
      TypeCat.ofHom (fun v ↦ (toGlueSheaf ι f').app X
        (Quot.mk (glueRel ι f' X.unop) (Sum.inl v))) ≫ (glueSheaf ι f').map g := sorry

/-- The canonical map from the U summand to the fppf quotient. -/
def inr {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : U ⟶ pushoutObj ι f' where
  app T := ↾fun v ↦ (toGlueSheaf ι f').app T
    (Quot.mk (glueRel ι f' T.unop) (Sum.inl v))
  naturality := by
    intro X Y g
    exact inr_naturality ι f' g

/-- A compatible pair of maps descends to the objectwise quotient by equalizing
every generating relation. -/
def gluePresheafDesc {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU) :
    gluePresheaf ι f' ⟶ B.functorOfPoints where
  app T := ↾(Quot.lift (uvHomApp hU hV)
    (fun _ _ hxy ↦ glueRel_hom_eq ι f' hV hU h hxy))
  naturality := by
    intro X Y g
    ext q
    exact (gluePresheaf_hom_natural ι f' hV hU h g.unop q).symm


/-- A compatible pair of maps extends to the sheafified quotient by étale descent. -/
def desc {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : pushoutObj ι f' ⟶ B :=
  Scheme.EtaleSheafification.desc (gluePresheaf ι f')
    ⟨B.functorOfPoints, B.isSheaf.of_le (Scheme.EtaleSheafification.etale_le_fppf_over S)⟩
    (gluePresheafDesc ι f' hV hU h)

/-- The descended map has the original compatible-pair formula on every generator. -/
theorem desc_toGlueSheaf_app {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f']
    (hV : V ⟶ B) (hU : U ⟶ B) (h : ι ≫ hV = f' ≫ hU)
    (T : (Over S)ᵒᵖ) (q : (gluePresheaf ι f').obj T) :
    (desc ι f' hV hU h).app T ((toGlueSheaf ι f').app T q) =
      (gluePresheafDesc ι f' hV hU h).app T q :=
  Scheme.EtaleSheafification.descendSection_toSheafify (gluePresheaf ι f')
    ⟨B.functorOfPoints, B.isSheaf.of_le (Scheme.EtaleSheafification.etale_le_fppf_over S)⟩ (gluePresheafDesc ι f' hV hU h) T.unop q

/-- The square `ι`, `f'`, `inl`, `inr` commutes. -/
theorem pushout_condition {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    ι ≫ inl ι f' = f' ≫ inr ι f' := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  apply congrArg ((toGlueSheaf ι f').app T)
  exact Quot.sound (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩))))

/-- Postcomposing `inl` with `desc` recovers the map from `V`. -/
theorem desc_inl {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : inl ι f' ≫ desc ι f' hV hU h = hV := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  exact desc_toGlueSheaf_app ι f' hV hU h T (Quot.mk _ (Sum.inr v))

/-- Postcomposing `inr` with `desc` recovers the map from `U`. -/
theorem desc_inr {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] (hV : V ⟶ B) (hU : U ⟶ B)
    (h : ι ≫ hV = f' ≫ hU) : inr ι f' ≫ desc ι f' hV hU h = hU := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro v
  exact desc_toGlueSheaf_app ι f' hV hU h T (Quot.mk _ (Sum.inl v))

/-- The explicit pushout cocone on `inl` and `inr`. -/
def pushoutCocone {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : PushoutCocone ι f' :=
  PushoutCocone.mk (inl ι f') (inr ι f') (pushout_condition ι f')

/-- Maps from the quotient are determined by their restrictions to both summands. -/
theorem pushout_hom_ext {U V V' B : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f']
    (h k : pushoutObj ι f' ⟶ B) (hV : inl ι f' ≫ h = inl ι f' ≫ k)
    (hU : inr ι f' ≫ h = inr ι f' ≫ k) : h = k := sorry

/-- The cocone on `pushoutObj` is a colimit cocone. -/
def pushoutCoconeIsColimit {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsColimit (pushoutCocone ι f') :=
  PushoutCocone.IsColimit.mk (pushout_condition ι f')
    (fun s ↦ desc ι f' s.inl s.inr s.condition)
    (fun s ↦ desc_inl ι f' s.inl s.inr s.condition)
    (fun s ↦ desc_inr ι f' s.inl s.inr s.condition)
    fun s m hV hU ↦ pushout_hom_ext ι f' m (desc ι f' s.inl s.inr s.condition)
      (hV.trans (desc_inl ι f' s.inl s.inr s.condition).symm)
      (hU.trans (desc_inr ι f' s.inl s.inr s.condition).symm)

/-- An open immersion and a separated étale morphism of algebraic spaces over `S`
have a pushout in `AlgebraicSpace S`. -/
instance instHasPushout {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : HasPushout ι f' :=
  HasColimit.mk ⟨pushoutCocone ι f', pushoutCoconeIsColimit ι f'⟩

/-- The canonical map `U ⟶ W` is an open immersion. -/
instance instIsOpenImmersion_inr {U V V' : AlgebraicSpace S} (ι : V' ⟶ V)
    (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsOpenImmersion (inr ι f') :=
  sorry

/-- The canonical map `V ⟶ W` is étale. -/
instance instEtale_inl {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] : Etale (inl ι f') :=
  sorry

/-- The canonical quotient square of an open immersion and a separated étale morphism
is a pushout in the category of algebraic spaces over the base. -/
@[stacks 0DVJ]
theorem isPushout_ofOpenSeparatedEtale {S : Scheme.{u}} {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsPushout ι f' (inl ι f') (inr ι f') :=
  IsPushout.of_isColimit (pushoutCoconeIsColimit ι f')

/-- The canonical quotient square of an open immersion and a separated étale morphism
is an elementary distinguished square. -/
@[stacks 0DVJ]
instance instIsElementaryDistinguishedSquare_ofOpenSeparatedEtale
    {S : Scheme.{u}} {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsElementaryDistinguishedSquare (inr ι f') (inl ι f') :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
