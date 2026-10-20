/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.OverField
public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The geometric-to-arithmetic fundamental-group homomorphism is injective. -/
theorem geometricToArithmetic_injective {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    Function.Injective (geometricToArithmetic X xbar) := sorry

/-- A connected finite étale object has preconnected underlying scheme. -/
theorem preconnectedSpace_of_isConnected_finiteEtale {B : Scheme.{u}} (V : FiniteEtale B)
    [IsConnected V] : PreconnectedSpace V.left := sorry

/-- The connected algebraic-closure base change forces preconnectedness after
pullback to any preconnected finite étale cover of the ground field (Stacks 0BTX). -/
theorem arithmeticBaseChange_preconnectedSpace {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace (geometricBaseChange X)]
    (V : FiniteEtale (Spec (CommRingCat.of k))) [PreconnectedSpace V.left] :
    PreconnectedSpace ((finiteEtaleBaseChange X.hom).obj V).left := sorry

/-- Geometric connectedness gives categorical connectedness. The inverse of a
nonempty monomorphism is the actual open-immersion lift of the identity. -/
theorem isConnected_finiteEtale_of_connectedSpace {B : Scheme.{u}} (V : FiniteEtale B)
    [ConnectedSpace V.left] : IsConnected V where
  notInitial := sorry
  noTrivialComponent W i mono hW := by
    classical
    letI : Mono i := mono
    have hnonempty : Nonempty W.left := by
      by_contra hempty
      letI : IsEmpty W.left := not_nonempty_iff.mp hempty
      apply hW
      exact CategoryTheory.Limits.IsInitial.ofUniqueHom
        (fun T ↦ MorphismProperty.Over.homMk
          ((AlgebraicGeometry.isInitialOfIsEmpty (X := W.left)).to T.left) (by
            exact (AlgebraicGeometry.isInitialOfIsEmpty (X := W.left)).hom_ext _ _))
        (by intro T f; sorry)
    letI : IsOpenImmersion i.left := FiniteEtale.mono_isOpenImmersion i
    have hcover : Set.range i.left = Set.univ :=
      IsClopen.eq_univ
        ⟨FiniteEtale.mono_isClosed_range i, i.left.isOpenEmbedding.isOpen_range⟩
        (Set.range_nonempty_iff_nonempty.mpr hnonempty)
    let reverse : V ⟶ W := MorphismProperty.Over.homMk
      (IsOpenImmersion.lift i.left (𝟙 V.left) (by rw [hcover]; exact Set.subset_univ _))
      (by sorry)
    exact ⟨⟨reverse, by sorry, by sorry⟩⟩

/-- Pullback along the structure map preserves connected finite étale objects,
with the inverse-bearing categorical field supplied by the native open lift. -/
theorem arithmeticBaseChange_isConnected {k : Type u} [Field k] (X : SchemeOverField k)
    [ConnectedSpace (geometricBaseChange X)]
    (V : FiniteEtale (Spec (CommRingCat.of k))) [IsConnected V]
    (v : ((finiteEtaleBaseChange X.hom).obj V).left) :
    IsConnected ((finiteEtaleBaseChange X.hom).obj V) := by
  letI : PreconnectedSpace V.left := preconnectedSpace_of_isConnected_finiteEtale V
  letI : ConnectedSpace ((finiteEtaleBaseChange X.hom).obj V).left :=
    { toPreconnectedSpace := arithmeticBaseChange_preconnectedSpace X V
      toNonempty := ⟨v⟩ }
  exact isConnected_finiteEtale_of_connectedSpace _

/-- The arithmetic-to-Galois fundamental-group homomorphism is surjective.
The lift witness comes from the native compactness construction for fiber
functor automorphisms, applied to the genuine base-change functor. -/
theorem arithmeticToGalois_surjective {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)] (ybar : GeometricPoint X.left) :
    Function.Surjective (arithmeticToGalois X ybar) := by
  letI : ConnectedSpace X.left :=
    { toPreconnectedSpace := (connectedSpace_of_geometricBaseChange X).toPreconnectedSpace
      toNonempty := ⟨ybar.hom default⟩ }
  let F := GeometricPoint.finiteFiber (galoisPoint X ybar)
  let F' := GeometricPoint.finiteFiber ybar
  let H := finiteEtaleBaseChange X.hom
  let t : H ⋙ F' ≅ F := GeometricPoint.finiteFiberBaseChangeIso X.hom ybar
  let h : Aut F' →ₜ* Aut F := GeometricPoint.fundamentalGroupMap X.hom ybar
  -- The action is restriction along the actual induced homomorphism.
  letI action (V : FiniteEtale (Spec (CommRingCat.of k))) :
      MulAction (Aut F') (F.obj V) := by
    letI : MulAction (Aut F) (F.obj V) := inferInstanceAs
      (MulAction (Aut (GeometricPoint.finiteFiber (galoisPoint X ybar)))
        ((GeometricPoint.finiteFiber (galoisPoint X ybar)).obj V))
    exact MulAction.compHom _ h.toMonoidHom
  letI naturalAction : IsNaturalSMul F (Aut F') :=
    { naturality := fun g V W f x ↦ by
        change F.map f ((h g).hom.app V x) = (h g).hom.app W (F.map f x)
        exact (ConcreteCategory.congr_hom ((h g).hom.naturality f) x).symm }
  letI continuousAction (V : FiniteEtale (Spec (CommRingCat.of k))) :
      ContinuousSMul (Aut F') (F.obj V) :=
    MulAction.continuousSMul_compHom (X := F.obj V) h.continuous
  have transitive (V : FiniteEtale (Spec (CommRingCat.of k))) [IsGalois V] :
      MulAction.IsPretransitive (Aut F') (F.obj V) := by
    refine ⟨fun x y ↦ ?_⟩
    let x' : F'.obj (H.obj V) := t.inv.app V x
    letI : IsConnected (H.obj V) :=
      arithmeticBaseChange_isConnected X V (x'.left (default : Spec (CommRingCat.of ybar.K)))
    let y' : F'.obj (H.obj V) := t.inv.app V y
    letI : MulAction (Aut F') (F'.obj (H.obj V)) := inferInstanceAs
      (MulAction (Aut ybar.finiteFiber) (ybar.finiteFiber.obj (H.obj V)))
    letI : MulAction.IsPretransitive (Aut F') (F'.obj (H.obj V)) :=
      FiberFunctor.isPretransitive_of_isConnected F' (H.obj V)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F') x' y'
    refine ⟨g, ?_⟩
    change t.hom.app V (g.hom.app (H.obj V) (t.inv.app V x)) = y
    change g.hom.app (H.obj V) (t.inv.app V x) = t.inv.app V y at hg
    exact (congrArg (fun z ↦ t.hom.app V z) hg).trans
      (FintypeCat.inv_hom_id_apply (t.app V) y)
  have native := toAut_surjective_of_isPretransitive F (Aut F') transitive
  have comparison : toAut F (Aut F') = h.toMonoidHom := by
    ext g V x
    rfl
  rw [comparison] at native
  exact native

/-- The image of the geometric fundamental group is the kernel of the arithmetic-to-Galois map. -/
theorem geometricToArithmetic_range_eq_arithmeticToGalois_ker
    {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    MonoidHom.range (geometricToArithmetic X xbar).hom.toMonoidHom =
      MonoidHom.ker (arithmeticToGalois X (arithmeticPoint X xbar)).hom.toMonoidHom :=
  sorry

/-- The geometric-arithmetic sequence of fundamental groups is short exact. -/
theorem geometricArithmetic_shortExact
    {k : Type u} [Field k] (X : SchemeOverField k)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) :
    Function.Injective (geometricToArithmetic X xbar) ∧
      MonoidHom.range (geometricToArithmetic X xbar).hom.toMonoidHom =
        MonoidHom.ker (arithmeticToGalois X (arithmeticPoint X xbar)).hom.toMonoidHom ∧
      Function.Surjective (arithmeticToGalois X (arithmeticPoint X xbar)) := sorry

end AlgebraicGeometry.SchemeOverField
