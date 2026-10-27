/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Preservation of finite nonempty limits and colimits

The aggregate classes are universe-stable and project automatically to each finite nonempty
shape. Binary (co)products together with the finite connected preservation classes form the
canonical construction interface.
-/

@[expose] public section

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor preserves finite nonempty limits if it preserves limits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyLimits (F : C ⥤ D) : Prop where
  /-- The functor preserves limits of every `Type`-small finite nonempty shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F

namespace PreservesFiniteNonemptyLimits

/-- Preservation of finite nonempty limits supplies preservation for finite nonempty shapes in
every universe. -/
instance (priority := 95) preservesLimitsOfShape
    (F : C ⥤ D) [PreservesFiniteNonemptyLimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesLimitsOfShape J F := by
  letI : Nonempty (FinCategory.AsType J) :=
    Nonempty.map (FinCategory.equivAsType J).inverse.obj (inferInstance : Nonempty J)
  letI := PreservesFiniteNonemptyLimits.out (F := F) (FinCategory.AsType J)
  exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

/-- Preservation of all finite limits implies preservation of finite nonempty limits. -/
instance (priority := 100) ofFiniteLimits
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteNonemptyLimits F := by
  exact ⟨fun J _ _ _ => inferInstance⟩

/-- A composite of functors preserving finite nonempty limits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteNonemptyLimits F] [PreservesFiniteNonemptyLimits G] :
    PreservesFiniteNonemptyLimits (F ⋙ G) := by
  exact ⟨fun J _ _ _ => inferInstance⟩

/-- Preservation of finite nonempty limits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyLimits G := by
  refine ⟨fun J _ _ _ => ?_⟩
  exact preservesLimitsOfShape_of_natIso e

/-- Preservation of finite nonempty limits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteNonemptyLimits F ↔ PreservesFiniteNonemptyLimits G := by
  constructor
  · intro h
    letI := h
    exact ofIso e
  · intro h
    letI := h
    exact ofIso e.symm

/-- Construct preservation of finite nonempty limits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesLimitsOfShape J F) :
    PreservesFiniteNonemptyLimits F := by
  refine ⟨fun J _ _ _ => ?_⟩
  letI : Category.{0} (ULift.{w} J) := uliftCategory J
  letI : Nonempty (ULiftHom.{w} (ULift.{w} J)) :=
    Nonempty.map (ULiftHomULiftCategory.objEquiv (C := J)).toFun
      (inferInstance : Nonempty J)
  letI := h (ULiftHom.{w} (ULift.{w} J))
  exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- A functor preserves finite nonempty limits if and only if it preserves every finite nonempty
shape in any fixed universe. -/
theorem iff_preservesLimitsOfShape (F : C ⥤ D) :
    PreservesFiniteNonemptyLimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        PreservesLimitsOfShape J F := by
  constructor
  · intro h J _ _ _
    letI := h
    infer_instance
  · exact ofSize F

/-- Preservation of finite nonempty limits includes preservation of finite connected limits. -/
instance (priority := 90) preservesFiniteConnectedLimits
    (F : C ⥤ D) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteConnectedLimits F := by
  exact ⟨fun J _ _ _ => PreservesFiniteNonemptyLimits.out J⟩

namespace BinaryProducts

private theorem preservesProductFinSucc
    (F : C ⥤ D) [HasFiniteNonemptyLimits C]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesFiniteConnectedLimits F] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), PreservesLimit (Discrete.functor f) F
  | 0, f => by
      letI : Nonempty (Discrete (Fin 1)) := ⟨⟨0⟩⟩
      letI := PreservesFiniteConnectedLimits.out (F := F) (Discrete (Fin 1))
      infer_instance
  | n + 1, f => by
      letI := preservesProductFinSucc F n
      letI : Nonempty (Discrete (Fin (n + 1))) := ⟨⟨0⟩⟩
      letI : Nonempty (Discrete WalkingPair) := ⟨⟨WalkingPair.left⟩⟩
      letI : HasLimitsOfShape (Discrete (Fin (n + 1))) C :=
        HasFiniteNonemptyLimits.out _
      letI : HasBinaryProducts C := HasFiniteNonemptyLimits.out _
      apply preservesLimit_of_preserves_limit_cone
        (CategoryTheory.extendFanIsLimit f (limit.isLimit _) (limit.isLimit _))
      apply (isLimitMapConeFanMkEquiv F _ _).symm _
      let hc := CategoryTheory.extendFanIsLimit (fun i => F.obj (f i))
        (isLimitOfHasProductOfPreservesLimit F _)
        (isLimitOfHasBinaryProductOfPreservesLimit F _ _)
      refine IsLimit.ofIsoLimit hc ?_
      refine Cone.ext (Iso.refl _) ?_
      rintro ⟨j⟩
      refine Fin.inductionOn j ?_ ?_
      · exact (Category.id_comp _).symm
      · intro i _
        change F.map (prod.snd : f 0 ⨯ (∏ᶜ fun k : Fin (n + 1) => f k.succ) ⟶ _) ≫
            F.map (Pi.π (fun k : Fin (n + 1) => f k.succ) i) =
          𝟙 _ ≫ F.map ((prod.snd : f 0 ⨯ (∏ᶜ fun k : Fin (n + 1) => f k.succ) ⟶ _) ≫
            Pi.π (fun k : Fin (n + 1) => f k.succ) i)
        rw [Category.id_comp, F.map_comp]

/-- Preservation of binary products and finite connected limits gives preservation of all finite
nonempty limits. -/
theorem ofFiniteConnected
    (F : C ⥤ D) [HasFiniteNonemptyLimits C]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesFiniteConnectedLimits F] :
    PreservesFiniteNonemptyLimits F := by
  have h (ι : Type) [Fintype ι] [Nonempty ι] :
      PreservesLimitsOfShape (Discrete ι) F := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    cases n with
    | zero =>
        obtain ⟨i⟩ := (inferInstance : Nonempty ι)
        exact Fin.elim0 (e i)
    | succ n =>
        letI : PreservesLimitsOfShape (Discrete (Fin (n + 1))) F := by
          refine ⟨fun {K} => ?_⟩
          letI := preservesProductFinSucc F n (fun i => K.obj ⟨i⟩)
          let eK : (Discrete.functor fun i : Fin (n + 1) => K.obj ⟨i⟩) ≅ K :=
            Discrete.natIso fun ⟨i⟩ => Iso.refl _
          exact preservesLimit_of_iso_diagram F eK
        exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F
  refine ⟨fun J _ _ _ => ?_⟩
  letI : Nonempty (Σ p : J × J, p.1 ⟶ p.2) :=
    Nonempty.map (fun j : J => ⟨(j, j), 𝟙 j⟩) (inferInstance : Nonempty J)
  letI : Nonempty (Discrete J) :=
    Nonempty.map Discrete.mk (inferInstance : Nonempty J)
  letI : Nonempty (Discrete (Σ p : J × J, p.1 ⟶ p.2)) :=
    Nonempty.map Discrete.mk (inferInstance : Nonempty (Σ p : J × J, p.1 ⟶ p.2))
  letI : HasLimitsOfShape (Discrete J) C := HasFiniteNonemptyLimits.out _
  letI : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
    HasFiniteNonemptyLimits.out _
  letI : HasEqualizers C := HasFiniteNonemptyLimits.out _
  letI := h J
  letI := h (Σ p : J × J, p.1 ⟶ p.2)
  letI := PreservesFiniteConnectedLimits.out (F := F) WalkingParallelPair
  exact preservesLimit_of_preservesEqualizers_and_product F

/-- For a functor whose source has finite nonempty limits, preservation of those limits is
equivalent to preservation of binary products and finite connected limits. -/
theorem iff_finiteConnected
    (F : C ⥤ D) [HasFiniteNonemptyLimits C] :
    PreservesFiniteNonemptyLimits F ↔
      PreservesLimitsOfShape (Discrete WalkingPair) F ∧
        PreservesFiniteConnectedLimits F := by
  constructor
  · intro h
    letI := h
    letI : Nonempty (Discrete WalkingPair) := ⟨⟨WalkingPair.left⟩⟩
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hprod, hconn⟩
    letI := hprod
    letI := hconn
    exact ofFiniteConnected F

end BinaryProducts

end PreservesFiniteNonemptyLimits

/-- A functor preserves finite nonempty colimits if it preserves colimits of every finite nonempty
shape. -/
class PreservesFiniteNonemptyColimits (F : C ⥤ D) : Prop where
  /-- The functor preserves colimits of every `Type`-small finite nonempty shape. -/
  out (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J F

namespace PreservesFiniteNonemptyColimits

/-- Preservation of finite nonempty colimits supplies preservation for finite nonempty shapes in
every universe. -/
instance (priority := 95) preservesColimitsOfShape
    (F : C ⥤ D) [PreservesFiniteNonemptyColimits F]
    (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J F := by
  letI : Nonempty (FinCategory.AsType J) :=
    Nonempty.map (FinCategory.equivAsType J).inverse.obj (inferInstance : Nonempty J)
  letI := PreservesFiniteNonemptyColimits.out (F := F) (FinCategory.AsType J)
  exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

/-- Preservation of all finite colimits implies preservation of finite nonempty colimits. -/
instance (priority := 100) ofFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteNonemptyColimits F := by
  exact ⟨fun J _ _ _ => inferInstance⟩

/-- A composite of functors preserving finite nonempty colimits preserves them. -/
instance (priority := 40) comp
    (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteNonemptyColimits F] [PreservesFiniteNonemptyColimits G] :
    PreservesFiniteNonemptyColimits (F ⋙ G) := by
  exact ⟨fun J _ _ _ => inferInstance⟩

/-- Preservation of finite nonempty colimits transfers across a natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} (e : F ≅ G) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyColimits G := by
  refine ⟨fun J _ _ _ => ?_⟩
  exact preservesColimitsOfShape_of_natIso e

/-- Preservation of finite nonempty colimits is invariant under natural isomorphism. -/
theorem iff_ofIso {F G : C ⥤ D} (e : F ≅ G) :
    PreservesFiniteNonemptyColimits F ↔ PreservesFiniteNonemptyColimits G := by
  constructor
  · intro h
    letI := h
    exact ofIso e
  · intro h
    letI := h
    exact ofIso e.symm

/-- Construct preservation of finite nonempty colimits by supplying it in any one universe. -/
theorem ofSize
    (F : C ⥤ D)
    (h : ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesColimitsOfShape J F) :
    PreservesFiniteNonemptyColimits F := by
  refine ⟨fun J _ _ _ => ?_⟩
  letI : Category.{0} (ULift.{w} J) := uliftCategory J
  letI : Nonempty (ULiftHom.{w} (ULift.{w} J)) :=
    Nonempty.map (ULiftHomULiftCategory.objEquiv (C := J)).toFun
      (inferInstance : Nonempty J)
  letI := h (ULiftHom.{w} (ULift.{w} J))
  exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- A functor preserves finite nonempty colimits if and only if it preserves every finite nonempty
shape in any fixed universe. -/
theorem iff_preservesColimitsOfShape (F : C ⥤ D) :
    PreservesFiniteNonemptyColimits F ↔
      ∀ (J : Type w) [SmallCategory J] [FinCategory J] [Nonempty J],
        PreservesColimitsOfShape J F := by
  constructor
  · intro h J _ _ _
    letI := h
    infer_instance
  · exact ofSize F

/-- Preservation of finite nonempty colimits includes preservation of finite connected
colimits. -/
instance (priority := 90) preservesFiniteConnectedColimits
    (F : C ⥤ D) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteConnectedColimits F := by
  exact ⟨fun J _ _ _ => PreservesFiniteNonemptyColimits.out J⟩

namespace BinaryCoproducts

/-- Preservation of binary coproducts and finite connected colimits gives preservation of all
finite nonempty colimits. -/
theorem ofFiniteConnected
    (F : C ⥤ D) [HasFiniteNonemptyColimits C]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesFiniteConnectedColimits F] :
    PreservesFiniteNonemptyColimits F := by
  letI : HasFiniteNonemptyLimits Cᵒᵖ := by
    refine ⟨fun J _ _ _ => ?_⟩
    letI := HasFiniteNonemptyColimits.out (C := C) Jᵒᵖ
    exact hasLimitsOfShape_op_of_hasColimitsOfShape
  letI : PreservesLimitsOfShape (Discrete WalkingPair) F.op := by
    letI : PreservesColimitsOfShape (Discrete WalkingPair)ᵒᵖ F :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite WalkingPair).symm F
    exact preservesLimitsOfShape_op _ F
  letI : PreservesFiniteConnectedLimits F.op := by
    refine ⟨fun J _ _ _ => ?_⟩
    letI := PreservesFiniteConnectedColimits.out (F := F) Jᵒᵖ
    exact preservesLimitsOfShape_op J F
  letI := PreservesFiniteNonemptyLimits.BinaryProducts.ofFiniteConnected F.op
  refine ⟨fun J _ _ _ => ?_⟩
  exact preservesColimitsOfShape_of_op J F

/-- For a functor whose source has finite nonempty colimits, preservation of those colimits is
equivalent to preservation of binary coproducts and finite connected colimits. -/
theorem iff_finiteConnected
    (F : C ⥤ D) [HasFiniteNonemptyColimits C] :
    PreservesFiniteNonemptyColimits F ↔
      PreservesColimitsOfShape (Discrete WalkingPair) F ∧
        PreservesFiniteConnectedColimits F := by
  constructor
  · intro h
    letI := h
    letI : Nonempty (Discrete WalkingPair) := ⟨⟨WalkingPair.left⟩⟩
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hprod, hconn⟩
    letI := hprod
    letI := hconn
    exact ofFiniteConnected F

end BinaryCoproducts

/-- Preservation of finite nonempty colimits by `F` is preservation of finite nonempty limits by
the opposite functor. -/
theorem iff_limits_op (F : C ⥤ D) :
    PreservesFiniteNonemptyColimits F ↔
      PreservesFiniteNonemptyLimits F.op := by
  constructor
  · intro h
    letI := h
    refine ⟨fun J _ _ _ => ?_⟩
    exact preservesLimitsOfShape_op J F
  · intro h
    letI := h
    refine ⟨fun J _ _ _ => ?_⟩
    exact preservesColimitsOfShape_of_op J F

/-- A functor preserving finite nonempty colimits induces an opposite functor preserving finite
nonempty limits. -/
theorem op (F : C ⥤ D) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyLimits F.op := by
  exact (iff_limits_op F).mp inferInstance

/-- A functor on opposite categories preserving finite nonempty colimits induces its unopposite
functor preserving finite nonempty limits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteNonemptyColimits F] :
    PreservesFiniteNonemptyLimits F.unop := by
  refine ⟨fun J _ _ _ => ?_⟩
  exact preservesLimitsOfShape_unop J F

end PreservesFiniteNonemptyColimits

namespace PreservesFiniteNonemptyLimits

/-- Preservation of finite nonempty limits by `F` is preservation of finite nonempty colimits by
the opposite functor. -/
theorem iff_colimits_op (F : C ⥤ D) :
    PreservesFiniteNonemptyLimits F ↔
      PreservesFiniteNonemptyColimits F.op := by
  constructor
  · intro h
    letI := h
    refine ⟨fun J _ _ _ => ?_⟩
    exact preservesColimitsOfShape_op J F
  · intro h
    letI := h
    refine ⟨fun J _ _ _ => ?_⟩
    exact preservesLimitsOfShape_of_op J F

/-- A functor preserving finite nonempty limits induces an opposite functor preserving finite
nonempty colimits. -/
theorem op (F : C ⥤ D) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyColimits F.op := by
  exact (iff_colimits_op F).mp inferInstance

/-- A functor on opposite categories preserving finite nonempty limits induces its unopposite
functor preserving finite nonempty colimits. -/
theorem unop (F : Cᵒᵖ ⥤ Dᵒᵖ) [PreservesFiniteNonemptyLimits F] :
    PreservesFiniteNonemptyColimits F.unop := by
  refine ⟨fun J _ _ _ => ?_⟩
  exact preservesColimitsOfShape_unop J F

end PreservesFiniteNonemptyLimits

end CategoryTheory.Limits

