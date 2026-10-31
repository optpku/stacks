/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Tactic.CrossRefAttribute
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.Over.Forget.LeftKanExtension

variable {C : Type u} [Category.{v} C]

namespace Index

/-- The discrete family of terminal objects used to calculate the left Kan extension along
`(Over.forget U).op` at `V`. -/
abbrev functor (U V : C) :
    Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (𝟙 ((Over.forget U).op.obj (op (Over.mk φ))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The discrete family of arrows `V ⟶ U` is final in the Kan-extension indexing category. -/
@[instance]
theorem final (U V : C) : Functor.Final (functor U V) where
  out d := by
    let φ : V ⟶ U := d.hom.unop ≫ d.left.unop.hom
    let g : d ⟶ (functor U V).obj ⟨φ⟩ :=
      CostructuredArrow.homMk
        ((Over.homMk d.hom.unop : Over.mk φ ⟶ d.left.unop).op)
        (by
          apply Quiver.Hom.unop_inj
          change 𝟙 V ≫ d.hom.unop = d.hom.unop
          exact Category.id_comp _)
    let t : StructuredArrow d (functor U V) := StructuredArrow.mk g
    apply isConnected_of_isTerminal _ (x := t)
    refine IsTerminal.ofUniqueHom (fun s => ?_) (fun s m => ?_)
    · rcases s with ⟨⟨⟨⟩⟩, ⟨ψ⟩, f⟩
      have hf : f.left.unop.left = d.hom.unop := by
        have h := congrArg Quiver.Hom.unop (CostructuredArrow.w f)
        change 𝟙 V ≫ f.left.unop.left = d.hom.unop at h
        change (f.left.unop.left : V ⟶ d.left.unop.left) = d.hom.unop
        simpa only [Category.id_comp] using h
      have hψ : ψ = φ := by
        have h := Over.w f.left.unop
        change f.left.unop.left ≫ d.left.unop.hom = ψ at h
        rw [hf] at h
        exact h.symm
      subst ψ
      refine StructuredArrow.homMk (𝟙 _) ?_
      rw [Functor.map_id, Category.comp_id]
      apply CostructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      exact hf
    · apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

/-- The restriction of the Kan-extension indexing diagram to `Index.functor U V` is the discrete
family of values of `G` on maps `V ⟶ U`. -/
abbrev projIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (V : C) :
    functor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) :=
  Discrete.natIso fun _ ↦ Iso.refl _

end Index

/-- The left Kan extension along `(Over.forget U).op` is objectwise the
coproduct of the values of `G` over maps `V ⟶ U`. -/
@[stacks 0494]
noncomputable def objIsoSigma
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (V : C) :
    ((Over.forget U).op.lan.obj G).obj (op V) ≅
      Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (Index.functor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (Index.projIso U G V) ≪≫
    Types.coproductIso.{v, max u w} (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

/-- The fiber of the left-Kan-extension sigma chart over a specified map is the corresponding
value of `G` in the slice category. -/
noncomputable def fiberIsoMk
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C} (φ : V ⟶ U) :
    {s : ((Over.forget U).op.lan.obj G).obj (op V) //
      ((objIsoSigma U G V).hom s).1 = φ} ≅
      G.obj (op (Over.mk φ)) :=
  ((Equiv.subtypeEquiv (objIsoSigma U G V).toEquiv (fun _ ↦ Iff.rfl)).trans
    (Equiv.sigmaSubtype φ)).toIso

/-- The fiber of the left-Kan-extension sigma chart over `X.hom` is canonically the value of `G`
at `X`. -/
noncomputable def fiberIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (X : Over U) :
    {s : ((Over.forget U).op.lan.obj G).obj (op X.left) //
      ((objIsoSigma U G X.left).hom s).1 = X.hom} ≅
      G.obj (op X) :=
  fiberIsoMk U G X.hom

/-- The fiber equivalence reads the second coordinate of the sigma chart, up to the dependent
type transport forced by the first-coordinate equality. -/
theorem fiberIso.hom_heq_snd
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (X : Over U)
    (s : ((Over.forget U).op.lan.obj G).obj (op X.left))
    (hs : ((objIsoSigma U G X.left).hom s).1 = X.hom) :
    HEq ((fiberIso U G X).hom ⟨s, hs⟩)
      ((objIsoSigma U G X.left).hom s).2 := by
  have h : ∀ (t : Σ a : X.left ⟶ U, G.obj (op (Over.mk a))) (ht : t.1 = X.hom),
      HEq ((Equiv.sigmaSubtype X.hom) ⟨t, ht⟩) t.2 := by
    rintro ⟨a, t⟩ ht
    change a = X.hom at ht
    subst a
    rfl
  exact h _ hs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sigma formula sends the unit generator associated to `a : V ⟶ U` to the corresponding
coproduct summand. -/
theorem objIsoSigma.hom_unitApp
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    (objIsoSigma U G V).hom
        (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a)) s) =
      ⟨a, s⟩ := by
  have h :
      ((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a)) ≫
        (objIsoSigma U G V).hom =
      ↾fun t ↦ (⟨a, t⟩ : Σ φ : V ⟶ U, G.obj (op (Over.mk φ))) := by
    simp only [objIsoSigma, Iso.trans_hom, Iso.symm_hom]
    erw [(Over.forget U).op.leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom_assoc
      G (op (Over.mk a))]
    erw [Functor.Final.ι_colimitIso_inv_assoc (Index.functor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G) ⟨a⟩]
    simp [Index.projIso]
  exact ConcreteCategory.congr_hom h s

/-- The inverse sigma chart sends a summand element to the corresponding left-Kan-extension
unit generator. -/
@[simp]
theorem objIsoSigma.inv_mk
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    (objIsoSigma U G V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := by
  apply (objIsoSigma U G V).toEquiv.injective
  simpa using (objIsoSigma.hom_unitApp U G a s).symm

/-- The inverse fiber chart has the expected underlying left-Kan-extension unit generator. -/
@[simp]
theorem fiberIsoMk.inv_val
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    ((fiberIsoMk U G a).inv s).1 =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := by
  change (objIsoSigma U G V).inv ⟨a, s⟩ = _
  exact objIsoSigma.inv_mk U G a s

/-- The inverse fiber chart at a slice object has the expected underlying unit generator. -/
@[simp]
theorem fiberIso.inv_val
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w))
    (X : Over U) (s : G.obj (op X)) :
    ((fiberIso U G X).inv s).1 =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op X)) s := by
  exact fiberIsoMk.inv_val U G X.hom s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In sigma coordinates, restriction along `f : Y ⟶ V` postcomposes the index and restricts its
section along the induced map in `Over U`. -/
theorem objIsoSigma.hom_map
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w))
    {V Y : C} (f : Y ⟶ V) (x : ((Over.forget U).op.lan.obj G).obj (op V)) :
    (objIsoSigma U G Y).hom (((Over.forget U).op.lan.obj G).map f.op x) =
      ⟨f ≫ ((objIsoSigma U G V).hom x).1,
        G.map
          (Over.homMk f :
            Over.mk (f ≫ ((objIsoSigma U G V).hom x).1) ⟶
              Over.mk ((objIsoSigma U G V).hom x).1).op
          ((objIsoSigma U G V).hom x).2⟩ := by
  obtain ⟨⟨a, s⟩, hx⟩ := (objIsoSigma U G V).toEquiv.symm.surjective x
  change (objIsoSigma U G V).inv ⟨a, s⟩ = x at hx
  subst x
  have h := ConcreteCategory.congr_hom
    (((Over.forget U).op.leftKanExtensionUnit G).naturality
      (Over.homMk f : Over.mk (f ≫ a) ⟶ Over.mk a).op) s
  change
    (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk (f ≫ a))))
        (G.map (Over.homMk f : Over.mk (f ≫ a) ⟶ Over.mk a).op s) =
      ((Over.forget U).op.lan.obj G).map f.op
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s) at h
  have hgen :
      (objIsoSigma U G Y).hom
        (((Over.forget U).op.lan.obj G).map f.op
          ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s)) =
      ⟨f ≫ a, G.map (Over.homMk f : Over.mk (f ≫ a) ⟶ Over.mk a).op s⟩ := by
    rw [← h, objIsoSigma.hom_unitApp]
  rw [objIsoSigma.inv_mk U G a s]
  exact hgen.trans (congrArg
    (fun t : Σ b : V ⟶ U, G.obj (op (Over.mk b)) ↦
      (⟨f ≫ t.1, G.map (Over.homMk f : Over.mk (f ≫ t.1) ⟶ Over.mk t.1).op t.2⟩ :
        Σ b : Y ⟶ U, G.obj (op (Over.mk b))))
    (objIsoSigma.hom_unitApp U G a s).symm)

private theorem unitApp_naturality
    (U : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v w)} (α : G ⟶ H)
    {V : C} (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    (((Over.forget U).op.lan.map α).app (op V))
        ((((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s) =
      (((Over.forget U).op.leftKanExtensionUnit H).app (op (Over.mk a)))
        (α.app (op (Over.mk a)) s) := by
  exact (ConcreteCategory.congr_hom
    (congr_app ((Over.forget U).op.lanUnit.naturality α) (op (Over.mk a))) s).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sigma chart acts on a morphism of input presheaves within each summand. -/
theorem objIsoSigma.hom_lan_map
    (U : C) {G H : (Over U)ᵒᵖ ⥤ Type (max u v w)} (α : G ⟶ H)
    (V : C) (x : ((Over.forget U).op.lan.obj G).obj (op V)) :
    (objIsoSigma U H V).hom ((((Over.forget U).op.lan.map α).app (op V)) x) =
      ⟨((objIsoSigma U G V).hom x).1,
        α.app (op (Over.mk ((objIsoSigma U G V).hom x).1))
          ((objIsoSigma U G V).hom x).2⟩ := by
  obtain ⟨⟨a, s⟩, hx⟩ := (objIsoSigma U G V).toEquiv.symm.surjective x
  change (objIsoSigma U G V).inv ⟨a, s⟩ = x at hx
  subst x
  rw [objIsoSigma.inv_mk U G a s, unitApp_naturality U α a s]
  exact (objIsoSigma.hom_unitApp U H a (α.app (op (Over.mk a)) s)).trans (congrArg
    (fun t : Σ b : V ⟶ U, G.obj (op (Over.mk b)) ↦
      (⟨t.1, α.app (op (Over.mk t.1)) t.2⟩ : Σ b : V ⟶ U, H.obj (op (Over.mk b))))
    (objIsoSigma.hom_unitApp U G a s).symm)

private theorem unitApp_injective
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C} (a : V ⟶ U) :
    Function.Injective
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) := by
  intro x y h
  have h' : (⟨a, x⟩ : Σ b : V ⟶ U, G.obj (op (Over.mk b))) = ⟨a, y⟩ :=
    (objIsoSigma.hom_unitApp U G a x).symm.trans
      ((congrArg (objIsoSigma U G V).hom h).trans (objIsoSigma.hom_unitApp U G a y))
  exact eq_of_heq (Sigma.mk.inj h').2

private theorem unitApp_fiberIsoMk_hom
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C} (a : V ⟶ U)
    (s : ((Over.forget U).op.lan.obj G).obj (op V))
    (hs : ((objIsoSigma U G V).hom s).1 = a) :
    (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a)))
        ((fiberIsoMk U G a).hom ⟨s, hs⟩) = s := by
  calc
    _ = ((fiberIsoMk U G a).inv ((fiberIsoMk U G a).hom ⟨s, hs⟩)).1 :=
      (fiberIsoMk.inv_val U G a ((fiberIsoMk U G a).hom ⟨s, hs⟩)).symm
    _ = s := by
      have h := (fiberIsoMk U G a).hom_inv_id_apply ⟨s, hs⟩
      exact congrArg
        (fun t : {t : ((Over.forget U).op.lan.obj G).obj (op V) //
          ((objIsoSigma U G V).hom t).1 = a} ↦ t.1) h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Left Kan extension along `(Over.forget U).op` preserves limits of
finite connected diagrams of type-valued presheaves. -/
@[stacks 0494, instance]
theorem preservesFiniteConnectedLimits (U : C) :
    PreservesFiniteConnectedLimits
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := by
  classical
  let L : ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v)) :=
    (Over.forget U).op.lan
  refine ⟨fun J _ _ _ ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
  refine ⟨evaluationJointlyReflectsLimits _ (fun W ↦ ?_)⟩
  apply Nonempty.some
  apply (Types.isLimit_iff _).2
  intro s hs
  -- Connectedness forces a coherent family to lie in a single sigma summand.
  let σ (j : J) := (objIsoSigma U (F.obj j) W.unop).hom (s j)
  have hσ (i j : J) (f : i ⟶ j) : (σ i).1 = (σ j).1 := by
    have h := congrArg (fun z ↦ ((objIsoSigma U (F.obj j) W.unop).hom z).1) (hs f)
    exact (congrArg Sigma.fst
      (objIsoSigma.hom_lan_map U (F.map f) W.unop (s i))).symm.trans h
  obtain ⟨a, ha⟩ := constant_of_preserves_morphisms' (fun j ↦ (σ j).1) hσ
  let y (j : J) : (F.obj j).obj (op (Over.mk a)) :=
    (fiberIsoMk U (F.obj j) a).hom ⟨s j, ha j⟩
  have hy (j : J) :
      (((Over.forget U).op.leftKanExtensionUnit (F.obj j)).app (op (Over.mk a)))
        (y j) = s j := unitApp_fiberIsoMk_hom U (F.obj j) a (s j) (ha j)
  have hn {i j : J} (f : i ⟶ j) :
      (F.map f).app (op (Over.mk a)) (y i) = y j := by
    apply unitApp_injective U (F.obj j) a
    calc
      _ = ((L.map (F.map f)).app W)
          ((((Over.forget U).op.leftKanExtensionUnit (F.obj i)).app
            (op (Over.mk a))) (y i)) := (unitApp_naturality U (F.map f) a (y i)).symm
      _ = s j := by rw [hy]; exact hs f
      _ = _ := (hy j).symm
  -- In that summand, use the original limit evaluated at `Over.mk a`.
  let E := (evaluation (Over U)ᵒᵖ (Type (max u v))).obj (op (Over.mk a))
  have he := isLimitOfPreserves E hc
  obtain ⟨t, ht, huniq⟩ := (Types.isLimit_iff _).1 ⟨he⟩ y (by
    intro i j f
    exact hn f)
  refine ⟨(((Over.forget U).op.leftKanExtensionUnit c.pt).app
    (op (Over.mk a))) t, ?_, ?_⟩
  · intro j
    change ((L.map (c.π.app j)).app W)
      ((((Over.forget U).op.leftKanExtensionUnit c.pt).app (op (Over.mk a))) t) = s j
    calc
      _ = (((Over.forget U).op.leftKanExtensionUnit (F.obj j)).app
          (op (Over.mk a))) ((E.mapCone c).π.app j t) :=
        unitApp_naturality U (c.π.app j) a t
      _ = _ := congrArg
        (((Over.forget U).op.leftKanExtensionUnit (F.obj j)).app (op (Over.mk a))) (ht j)
      _ = s j := hy j
  · intro z hz
    have hza : ((objIsoSigma U c.pt W.unop).hom z).1 = a := by
      let j : J := Classical.arbitrary J
      calc
        _ = ((objIsoSigma U (F.obj j) W.unop).hom
            (((L.map (c.π.app j)).app W) z)).1 :=
          (congrArg Sigma.fst (objIsoSigma.hom_lan_map U (c.π.app j) W.unop z)).symm
        _ = (σ j).1 := congrArg (fun q ↦ ((objIsoSigma U (F.obj j) W.unop).hom q).1)
          (hz j)
        _ = a := ha j
    let z' := (fiberIsoMk U c.pt a).hom ⟨z, hza⟩
    have hηz :
        (((Over.forget U).op.leftKanExtensionUnit c.pt).app (op (Over.mk a))) z' = z :=
      unitApp_fiberIsoMk_hom U c.pt a z hza
    have hz' (j : J) : (E.mapCone c).π.app j z' = y j := by
      apply unitApp_injective U (F.obj j) a
      calc
        _ = ((L.map (c.π.app j)).app W)
            ((((Over.forget U).op.leftKanExtensionUnit c.pt).app
              (op (Over.mk a))) z') := (unitApp_naturality U (c.π.app j) a z').symm
        _ = s j := by rw [hηz]; exact hz j
        _ = _ := (hy j).symm
    calc
      z = _ := hηz.symm
      _ = _ := congrArg
        (((Over.forget U).op.leftKanExtensionUnit c.pt).app (op (Over.mk a)))
        (huniq z' hz')

/-- The presheaf-level localization lower shriek preserves pullbacks. -/
@[stacks 0494]
theorem preservesPullbacks (U : C) :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := by
  exact @PreservesFiniteConnectedLimits.out _ _ _ _ _
    (preservesFiniteConnectedLimits U) WalkingCospan _ _ _

/-- The presheaf-level localization lower shriek preserves equalizers. -/
@[stacks 0494]
theorem preservesEqualizers (U : C) :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := by
  exact @PreservesFiniteConnectedLimits.out _ _ _ _ _
    (preservesFiniteConnectedLimits U) WalkingParallelPair _ _ _

end CategoryTheory.Over.Forget.LeftKanExtension
