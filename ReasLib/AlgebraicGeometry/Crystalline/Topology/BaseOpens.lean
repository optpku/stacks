/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Topos
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
      (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restriction of a relative crystalline object to the inverse image of a base open. -/
def restrictBaseOpen (V : S.Opens) (C : RelativeCRIS S I γ hc X x₀) :
    RelativeCRIS S I γ hc X x₀ :=
  relativeRestrictOpen C (C.1.thickeningToBase ⁻¹ᵁ V)

/-- A crystalline morphism restricts to the inverse images of a base open. -/
def restrictBaseOpenMap (V : S.Opens) {T C : RelativeCRIS S I γ hc X x₀}
    (k : T ⟶ C) : restrictBaseOpen V T ⟶ restrictBaseOpen V C :=
  Eq.mp (congrArg (fun U => CrystallineObject.Hom (CrystallineObject.restrictOpen T.1 U)
    (restrictBaseOpen V C).1) (congrArg (fun b => b ⁻¹ᵁ V) k.base_comm))
      (CrystallineObject.Hom.restrictOpen k (C.1.thickeningToBase ⁻¹ᵁ V))

/-- Base-open restriction preserves identity morphisms. -/
theorem restrictBaseOpen_map_id (V : S.Opens) (C : RelativeCRIS S I γ hc X x₀) :
    restrictBaseOpenMap V (𝟙 C) = 𝟙 (restrictBaseOpen V C) := sorry

/-- Base-open restriction preserves composition of crystalline morphisms. -/
theorem restrictBaseOpen_map_comp (V : S.Opens) {T C D : RelativeCRIS S I γ hc X x₀}
    (k : T ⟶ C) (l : C ⟶ D) :
    restrictBaseOpenMap V (k ≫ l) = restrictBaseOpenMap V k ≫ restrictBaseOpenMap V l := sorry

/-- Restriction to the inverse image of a base open is functorial. -/
def restrictBaseOpenFunctor (V : S.Opens) :
    RelativeCRIS S I γ hc X x₀ ⥤ RelativeCRIS S I γ hc X x₀ where
  obj := restrictBaseOpen V
  map := restrictBaseOpenMap V
  map_id := restrictBaseOpen_map_id V
  map_comp := restrictBaseOpen_map_comp V

/-- Restriction to a base open preserves small crystalline objects and is supported on that open. -/
theorem restrictBaseOpen_small (V : S.Opens)
    (C : smallCrystallineSite S I γ hc X x₀) :
    IsOpenImmersion (restrictBaseOpen V C.obj).1.source.hom ∧
      (restrictBaseOpen V C.obj).1.thickeningToBase ⁻¹ᵁ V = ⊤ := sorry

/-- Restriction of a small crystalline object to a base open. -/
def restrictBaseOpenSmall (V : S.Opens) (C : smallCrystallineSite S I γ hc X x₀) :
    smallCrystallineSite S I γ hc X x₀ :=
  ⟨restrictBaseOpen V C.obj, (restrictBaseOpen_small V C).1⟩

/-- The open inclusions on source and thickening satisfy the crystalline constructor laws. -/
theorem restrictBaseOpen_ι_laws (V : S.Opens) (C : RelativeCRIS S I γ hc X x₀) :
    let U := C.1.thickeningToBase ⁻¹ᵁ V
    let R := restrictBaseOpen V C
    ((C.1.inclusion ⁻¹ᵁ U).ι ≫ C.1.source.hom = R.1.source.hom) ∧
    ((C.1.inclusion ⁻¹ᵁ U).ι ≫ C.1.inclusion = R.1.inclusion ≫ U.ι) ∧
    (U.ι ≫ C.1.thickeningToBase = R.1.thickeningToBase) ∧
    (C.1.ideal.comap U.ι ≤ R.1.ideal) ∧
    (∀ (W : C.1.thickening.affineOpens) (W' : R.1.thickening.affineOpens)
      (hWW' : W'.1 ≤ U.ι ⁻¹ᵁ W.1),
      (C.1.gamma W).IsDPMorphism (R.1.gamma W') (U.ι.appLE W.1 W'.1 hWW').hom) := sorry

/-- The crystalline inclusion of a restriction to a base open. -/
def restrictBaseOpenι (V : S.Opens) (C : RelativeCRIS S I γ hc X x₀) :
    restrictBaseOpen V C ⟶ C where
  source := Over.homMk (C.1.inclusion ⁻¹ᵁ (C.1.thickeningToBase ⁻¹ᵁ V)).ι
    (restrictBaseOpen_ι_laws V C).1
  thickening := (C.1.thickeningToBase ⁻¹ᵁ V).ι
  source_comm := (restrictBaseOpen_ι_laws V C).2.1
  base_comm := (restrictBaseOpen_ι_laws V C).2.2.1
  ideal_compatible := (restrictBaseOpen_ι_laws V C).2.2.2.1
  dividedPowers_compatible := (restrictBaseOpen_ι_laws V C).2.2.2.2

/-- Support of the domain on a base open implies support of both component maps over its inverse image. -/
theorem restrictBaseOpen_support_preimage (V : S.Opens)
    {T C : RelativeCRIS S I γ hc X x₀} (k : T ⟶ C)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    k.thickening ⁻¹ᵁ (C.1.thickeningToBase ⁻¹ᵁ V) = ⊤ ∧
      k.source.left ⁻¹ᵁ (C.1.inclusion ⁻¹ᵁ (C.1.thickeningToBase ⁻¹ᵁ V)) = ⊤ := sorry

/-- The thickening map with codomain restricted to a base open containing its image. -/
private def supportedThickeningMap (V : S.Opens)
    {T C : RelativeCRIS S I γ hc X x₀} (k : T ⟶ C)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    T.1.thickening ⟶ (restrictBaseOpen V C).1.thickening :=
  T.1.thickening.topIso.inv ≫
    (T.1.thickening.isoOfEq (restrictBaseOpen_support_preimage V k q).1.symm).hom ≫
      (k.thickening ∣_ (C.1.thickeningToBase ⁻¹ᵁ V))

/-- The source map with codomain restricted to the open containing its image. -/
private def supportedSourceMap (V : S.Opens)
    {T C : RelativeCRIS S I γ hc X x₀} (k : T ⟶ C)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    T.1.source.left ⟶ (restrictBaseOpen V C).1.source.left :=
  T.1.source.left.topIso.inv ≫
    (T.1.source.left.isoOfEq (restrictBaseOpen_support_preimage V k q).2.symm).hom ≫
      (k.source.left ∣_ (C.1.inclusion ⁻¹ᵁ (C.1.thickeningToBase ⁻¹ᵁ V)))

/-- The supported source and thickening maps satisfy the crystalline constructor laws. -/
theorem restrictBaseOpen_lift_laws (V : S.Opens)
    {T C : RelativeCRIS S I γ hc X x₀} (k : T ⟶ C)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    let R := restrictBaseOpen V C
    let a := supportedSourceMap V k q
    let b := supportedThickeningMap V k q
    (a ≫ R.1.source.hom = T.1.source.hom) ∧
    (a ≫ R.1.inclusion = T.1.inclusion ≫ b) ∧
    (b ≫ R.1.thickeningToBase = T.1.thickeningToBase) ∧
    (R.1.ideal.comap b ≤ T.1.ideal) ∧
    (∀ (W : R.1.thickening.affineOpens) (W' : T.1.thickening.affineOpens)
      (hWW' : W'.1 ≤ b ⁻¹ᵁ W.1),
      (R.1.gamma W).IsDPMorphism (T.1.gamma W') (b.appLE W.1 W'.1 hWW').hom) := sorry

/-- A crystalline morphism whose domain is supported on a base open factors into the restriction. -/
def restrictBaseOpenLift (V : S.Opens) {T C : RelativeCRIS S I γ hc X x₀}
    (k : T ⟶ C) (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    T ⟶ restrictBaseOpen V C where
  source := Over.homMk (supportedSourceMap V k q) (restrictBaseOpen_lift_laws V k q).1
  thickening := supportedThickeningMap V k q
  source_comm := (restrictBaseOpen_lift_laws V k q).2.1
  base_comm := (restrictBaseOpen_lift_laws V k q).2.2.1
  ideal_compatible := (restrictBaseOpen_lift_laws V k q).2.2.2.1
  dividedPowers_compatible := (restrictBaseOpen_lift_laws V k q).2.2.2.2

/-- Composing the supported lift with the open inclusion recovers the original crystalline morphism. -/
theorem restrictBaseOpen_factorization (V : S.Opens)
    {T C : RelativeCRIS S I γ hc X x₀} (k : T ⟶ C)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤) :
    CrystallineObject.Hom.comp (restrictBaseOpenLift V k q) (restrictBaseOpenι V C) = k := sorry

/-- The subterminal presheaf of crystalline thickenings supported on a base open. -/
def baseOpenPresheaf (V : S.Opens) :
    (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift (PLift (T.unop.1.thickeningToBase ⁻¹ᵁ V = ⊤))
  map k := ↾fun q => ⟨⟨(congrArg (fun b => b ⁻¹ᵁ V) k.unop.base_comm).symm.trans
    (congrArg (fun U => k.unop.thickening ⁻¹ᵁ U) q.down.down)⟩⟩
  map_id _ := ConcreteCategory.hom_ext _ _ (fun _ => Subsingleton.elim _ _)
  map_comp _ _ := ConcreteCategory.hom_ext _ _ (fun _ => Subsingleton.elim _ _)

/-- The support presheaf of a base open satisfies crystalline Zariski descent. -/
theorem baseOpen_isSheaf (V : S.Opens) :
    Presheaf.IsSheaf (crystallineZariskiTopology S I γ hc X x₀)
      (baseOpenPresheaf V) := sorry

/-- The subterminal crystalline sheaf of thickenings supported on a base open. -/
def baseOpenSheaf (V : S.Opens) :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1)) :=
  ⟨baseOpenPresheaf V, baseOpen_isSheaf V⟩

variable (p : ℕ) [Fact p.Prime]
  (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
  (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The presheaf underlying the terminal small crystalline sheaf. -/
private abbrev smallTerminalPresheaf :=
  (⊤_ (Sheaf (smallCrystallineTopology p S I γ hc s X x₀ hp) (Type (u + 1)))).obj

/-- The left Kan extension of the terminal small crystalline sheaf's presheaf. -/
private abbrev terminalExtensionPresheaf :=
  (smallCrystallineInclusion S I γ hc X x₀).op.leftKanExtension
    (smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp)

/-- The left Kan extension of the restriction of a base-open support presheaf. -/
private abbrev baseOpenExtensionPresheaf (V : S.Opens) :=
  (smallCrystallineInclusion S I γ hc X x₀).op.leftKanExtension
    ((smallCrystallineInclusion S I γ hc X x₀).op ⋙ baseOpenPresheaf V)

/-- A supported Kan-extension generator is sent to the restricted small thickening and its supported lift. -/
private def baseOpenKanGenerator (V : S.Opens) (T : RelativeCRIS S I γ hc X x₀)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤)
    (j : CostructuredArrow (smallCrystallineInclusion S I γ hc X x₀).op (op T)) :
    (baseOpenExtensionPresheaf V).obj (op T) :=
  ((baseOpenExtensionPresheaf V).map (restrictBaseOpenLift V j.hom.unop q).op)
    (((smallCrystallineInclusion S I γ hc X x₀).op.leftKanExtensionUnit
      ((smallCrystallineInclusion S I γ hc X x₀).op ⋙ baseOpenPresheaf V)).app
        (op (restrictBaseOpenSmall V j.left.unop))
          ⟨⟨(restrictBaseOpen_small V j.left.unop).2⟩⟩)

/-- Supported Kan-extension generators respect the relations of the pointwise colimit. -/
theorem baseOpenKanLift_rel (V : S.Opens) (T : RelativeCRIS S I γ hc X x₀)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤)
    {j j' : CostructuredArrow (smallCrystallineInclusion S I γ hc X x₀).op (op T)}
    (a : j ⟶ j') :
    ((CostructuredArrow.proj (smallCrystallineInclusion S I γ hc X x₀).op (op T) ⋙
      smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).map a) ≫
        (↾fun _ => baseOpenKanGenerator V T q j') =
      (↾fun _ => baseOpenKanGenerator V T q j) := sorry

/-- The supported pairing on a pointwise Kan-extension colimit, defined by its canonical injections. -/
private def baseOpenKanLiftApp (V : S.Opens) (T : (RelativeCRIS S I γ hc X x₀)ᵒᵖ) :
    ((baseOpenPresheaf V ⨯
      terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).obj T) ⟶
        (baseOpenExtensionPresheaf V).obj T :=
  ↾fun x =>
    let q := ((prod.fst : baseOpenPresheaf V ⨯
      terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp ⟶
        baseOpenPresheaf V).app T x).down.down
    let D := CostructuredArrow.proj (smallCrystallineInclusion S I γ hc X x₀).op T ⋙
      smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp
    (colimit.desc D
      { pt := (baseOpenExtensionPresheaf V).obj T
        ι :=
          { app := fun j => ↾fun _ => baseOpenKanGenerator V T.unop q j
            naturality := fun _ _ a => baseOpenKanLift_rel p s hp V T.unop q a } })
      (((smallCrystallineInclusion S I γ hc X x₀).op.leftKanExtensionObjIsoColimit
        (smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp) T).hom
          ((prod.snd : baseOpenPresheaf V ⨯
            terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp ⟶
              terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).app T x))

/-- The supported pointwise Kan-extension pairing commutes with restriction. -/
theorem baseOpenKanLift_naturality (V : S.Opens)
    {T T' : (RelativeCRIS S I γ hc X x₀)ᵒᵖ} (k : T ⟶ T') :
    (baseOpenPresheaf V ⨯
      terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).map k ≫
        baseOpenKanLiftApp p s hp V T' =
      baseOpenKanLiftApp p s hp V T ≫ (baseOpenExtensionPresheaf V).map k := sorry

/-- The supported pairing from a base-open presheaf times the extension of the terminal presheaf. -/
def baseOpenKanLift (V : S.Opens) :
    baseOpenPresheaf V ⨯
      terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp ⟶
        baseOpenExtensionPresheaf V where
  app := baseOpenKanLiftApp p s hp V
  naturality := fun _ _ k => baseOpenKanLift_naturality p s hp V k

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]

/-- Extension of the restriction of the support sheaf to the small crystalline site. -/
def baseOpenExtension (V : S.Opens) :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1)) :=
  ((smallCrystallineInclusion S I γ hc X x₀).sheafPullback (Type (u + 1))
    (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (crystallineZariskiTopology S I γ hc X x₀)).obj
      (((smallCrystallineInclusion S I γ hc X x₀).sheafPushforwardContinuous (Type (u + 1))
        (smallCrystallineTopology p S I γ hc s X x₀ hp)
        (crystallineZariskiTopology S I γ hc X x₀)).obj (baseOpenSheaf V))

/-- The extension-to-support map is the counit of continuous crystalline restriction. -/
def baseOpenExtensionHom (V : S.Opens) : baseOpenExtension (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V ⟶ baseOpenSheaf V :=
  ((smallCrystallineInclusion S I γ hc X x₀).sheafAdjunctionContinuous (Type (u + 1))
    (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (crystallineZariskiTopology S I γ hc X x₀)).counit.app (baseOpenSheaf V)

/-- The support-to-extension map is the sheafified supported pairing using the canonical terminal section. -/
def baseOpenExtensionInv (V : S.Opens) : baseOpenSheaf V ⟶ baseOpenExtension (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V :=
  let a := presheafToSheaf (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))
  let L := (smallCrystallineInclusion S I γ hc X x₀).sheafPullback (Type (u + 1))
    (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (crystallineZariskiTopology S I γ hc X x₀)
  let e := Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallCrystallineInclusion S I γ hc X x₀) (Type (u + 1))
    (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (crystallineZariskiTopology S I γ hc X x₀)
  prod.lift (sheafificationIso (baseOpenSheaf V)).hom
      (terminal.from (baseOpenSheaf V) ≫ (PreservesTerminal.iso L).inv ≫ e.hom.app (⊤_ _)) ≫
    (PreservesLimitPair.iso a (baseOpenPresheaf V)
      (terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp)).inv ≫
    a.map (baseOpenKanLift p s hp V) ≫
    e.inv.app (((smallCrystallineInclusion S I γ hc X x₀).sheafPushforwardContinuous
      (Type (u + 1)) (smallCrystallineTopology p S I γ hc s X x₀ hp)
        (crystallineZariskiTopology S I γ hc X x₀)).obj (baseOpenSheaf V))

/-- The extension counit followed by the supported inverse is the identity. -/
theorem baseOpenExtension_hom_inv_id (V : S.Opens) :
    baseOpenExtensionHom (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V ≫ baseOpenExtensionInv (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V =
      𝟙 (baseOpenExtension (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V) := sorry

/-- The supported inverse followed by the extension counit is the identity. -/
theorem baseOpenExtension_inv_hom_id (V : S.Opens) :
    baseOpenExtensionInv (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V ≫ baseOpenExtensionHom (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V =
      𝟙 (baseOpenSheaf V) := sorry

/-- Extension after small-site restriction fixes crystalline sheaves supported on a base open. -/
def baseOpenExtensionIso (V : S.Opens) : baseOpenExtension (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V ≅ baseOpenSheaf V where
  hom := baseOpenExtensionHom (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V
  inv := baseOpenExtensionInv (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V
  hom_inv_id := baseOpenExtension_hom_inv_id p s hp V
  inv_hom_id := baseOpenExtension_inv_hom_id p s hp V

/-- Inclusion of base opens induces inclusion of their crystalline support sheaves. -/
def baseOpenSheafMap {V W : S.Opens} (h : V ≤ W) :
    baseOpenSheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) V ⟶ baseOpenSheaf W where
  hom :=
    { app := fun T => ↾fun q => ⟨⟨top_unique
        (q.down.down ▸ (TopologicalSpace.Opens.map T.unop.1.thickeningToBase.base).monotone h)⟩⟩
      naturality := fun T T' _ => ConcreteCategory.hom_ext _ _
        (fun _ => @Subsingleton.elim
          (ULift (PLift (T'.unop.1.thickeningToBase ⁻¹ᵁ W = ⊤))) inferInstance _ _) }

/-- The supported extension inverse is natural under inclusion of base opens. -/
theorem baseOpenExtension_naturality {V W : S.Opens} (h : V ≤ W) :
    baseOpenSheafMap h ≫ baseOpenExtensionInv (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp W =
      baseOpenExtensionInv (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp V ≫
        ((smallCrystallineInclusion S I γ hc X x₀).sheafPullback (Type (u + 1))
          (smallCrystallineTopology p S I γ hc s X x₀ hp)
          (crystallineZariskiTopology S I γ hc X x₀)).map
            (((smallCrystallineInclusion S I γ hc X x₀).sheafPushforwardContinuous
              (Type (u + 1)) (smallCrystallineTopology p S I γ hc s X x₀ hp)
              (crystallineZariskiTopology S I γ hc X x₀)).map (baseOpenSheafMap h)) := sorry

/-- On a supported generator the Kan pairing uses the restriction of its small thickening and the supported lift. -/
theorem baseOpenExtensionIso_spec (V : S.Opens) (T : RelativeCRIS S I γ hc X x₀)
    (q : T.1.thickeningToBase ⁻¹ᵁ V = ⊤)
    (j : CostructuredArrow (smallCrystallineInclusion S I γ hc X x₀).op (op T))
    (a : (smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).obj j.left) :
    let t := (((smallCrystallineInclusion S I γ hc X x₀).op.leftKanExtensionUnit
      (smallTerminalPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp)).app j.left ≫
        (terminalExtensionPresheaf (I := I) (γ := γ) (hc := hc) (x₀ := x₀) p s hp).map j.hom) a
    ((prod.lift (uliftYonedaEquiv.{u + 1}.symm (ULift.up (PLift.up q)))
      (uliftYonedaEquiv.{u + 1}.symm t) ≫ baseOpenKanLift p s hp V).app (op T)) (ULift.up (𝟙 T)) =
        baseOpenKanGenerator V T q j := sorry

end AlgebraicGeometry.Scheme.Crystalline
