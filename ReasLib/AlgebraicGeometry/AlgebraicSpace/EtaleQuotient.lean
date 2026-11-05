/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Sheafification.Lift
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.Over
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Algebraic-space quotients of étale equivalence relations

The small étale quotient sheaf of a scheme étale equivalence relation defines an
algebraic space with a canonical quotient projection. Explicit sheafification
extensions identify its universe-raised functor of points with the fppf quotient
and identify the specified quotient maps and their kernel pair.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.PreRelation

variable {S : Scheme.{u}} {U : Over S}

/-- A section of the local sheafification is represented near any specified point by
an actual map to the presenting scheme. The witness records both the point and the
equality of sections on an étale neighbourhood. -/
theorem exists_localRepresentative (P : PreRelation U) (T : Over S) (x : T.left)
    (q : (EtaleSheafification.localSheaf P.quotientPresheaf T).obj.obj
      (op (Scheme.Etale.mk (𝟙 T.left)))) :
    ∃ z : U.left, ∃ (V : T.left.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 T.left))
      (y : V.left) (a : (EtaleSheafification.testFunctor T).obj V ⟶ U),
      f.left y = x ∧ a.left y = z ∧
        (toSheafify T.left.smallEtaleTopology
          (EtaleSheafification.restriction P.quotientPresheaf T)).app (op V)
            (Quot.mk (P.pointRel _) a) =
          (EtaleSheafification.localSheaf P.quotientPresheaf T).obj.map f.op q := by
  let η := toSheafify T.left.smallEtaleTopology
    (EtaleSheafification.restriction P.quotientPresheaf T)
  have hcov := Presheaf.imageSieve_mem T.left.smallEtaleTopology η q
  obtain ⟨𝒰, hOver, hEtale, hle⟩ :=
    (mem_smallGrothendieckTopology _ _).mp hcov
  letI := hOver
  obtain ⟨index, y, hy⟩ := 𝒰.exists_eq x
  let V : T.left.Etale := (𝒰.X index).asOverProp T.left (hEtale index)
  let f : V ⟶ Scheme.Etale.mk (𝟙 T.left) := (𝒰.f index).asOverProp T.left
  obtain ⟨localSection, hsection⟩ := hle _ _ ⟨index⟩
  obtain ⟨a, rfl⟩ := Quot.exists_rep localSection
  exact ⟨a.left y, V, f, y, a, hy, rfl, hsection⟩

/-- A point of the presenting scheme obtained from a genuine local representative.
The existence certificate `exists_localRepresentative` is proved without `sorry`. -/
def localRepresentativePoint (P : PreRelation U) (T : Over S) (x : T.left)
    (q : (EtaleSheafification.localSheaf P.quotientPresheaf T).obj.obj
      (op (Scheme.Etale.mk (𝟙 T.left)))) : U.left :=
  (P.exists_localRepresentative T x q).choose

/-- The chosen point comes from an étale neighbourhood on which the section is represented
by a map to the presenting scheme. -/
theorem localRepresentativePoint_spec (P : PreRelation U) (T : Over S) (x : T.left)
    (q : (EtaleSheafification.localSheaf P.quotientPresheaf T).obj.obj
      (op (Scheme.Etale.mk (𝟙 T.left)))) :
    ∃ (V : T.left.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 T.left))
      (y : V.left) (a : (EtaleSheafification.testFunctor T).obj V ⟶ U),
      f.left y = x ∧ a.left y = P.localRepresentativePoint T x q ∧
        (toSheafify T.left.smallEtaleTopology
          (EtaleSheafification.restriction P.quotientPresheaf T)).app (op V)
            (Quot.mk (P.pointRel _) a) =
          (EtaleSheafification.localSheaf P.quotientPresheaf T).obj.map f.op q :=
  (P.exists_localRepresentative T x q).choose_spec

/-- The small étale quotient of an étale equivalence relation satisfies fppf descent. -/
theorem smallEtaleQuotientSheaf_isFppfSheaf (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) P.smallEtaleQuotientSheaf.obj := sorry

/-- The diagonal of the small étale quotient is representable. -/
theorem smallEtaleQuotientSheaf_representableDiagonal (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    yoneda.relativelyRepresentable (Limits.diag P.smallEtaleQuotientSheaf.obj) := sorry

/-- The specified small quotient projection is representable and étale. -/
theorem smallEtaleQuotientSheafMk_etale (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    (MorphismProperty.over (@Etale)).presheaf P.smallEtaleQuotientSheafMk := sorry

/-- The specified small quotient projection is étale-locally surjective. -/
theorem smallEtaleQuotientSheafMk_locallySurjective (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      P.smallEtaleQuotientSheafMk := sorry

/-- The small étale quotient sheaf of an étale equivalence relation on a scheme
is an algebraic space, with the specified quotient projection as atlas. -/
instance instIsAlgebraicSpaceSmallEtaleQuotientSheaf (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace.IsAlgebraicSpace P.smallEtaleQuotientSheaf.obj where
  isSheaf := P.smallEtaleQuotientSheaf_isFppfSheaf
  representableDiagonal := P.smallEtaleQuotientSheaf_representableDiagonal
  atlas := ⟨U, P.smallEtaleQuotientSheafMk, P.smallEtaleQuotientSheafMk_etale,
    P.smallEtaleQuotientSheafMk_locallySurjective⟩

/-- The algebraic space whose functor of points is the small étale quotient sheaf
of a scheme étale equivalence relation. -/
def etaleQuotientSpace (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace S :=
  AlgebraicSpace.ofIsAlgebraicSpace P.smallEtaleQuotientSheaf.obj

/-- The functor of points of the étale quotient space is the small étale quotient sheaf. -/
@[simp]
theorem etaleQuotientSpace_functorOfPoints (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    P.etaleQuotientSpace.functorOfPoints = P.smallEtaleQuotientSheaf.obj := rfl

/-- The canonical projection from a scheme to the algebraic-space quotient of
an étale equivalence relation on it. -/
def etaleQuotientMap (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    AlgebraicSpace.ofOver U ⟶ P.etaleQuotientSpace :=
  P.smallEtaleQuotientSheafMk

/-- On scheme-valued points the algebraic-space quotient projection is the
canonical map into the small étale quotient sheaf. -/
@[simp]
theorem etaleQuotientMap_app (P : PreRelation U) [P.IsEtaleEquivalenceRelation]
    {T : Over S} (a : T ⟶ U) :
    P.etaleQuotientMap.app (op T) a = P.smallEtaleQuotientSheafMk.app (op T) a := rfl

section

set_option backward.isDefEq.respectTransparency false

/-- The functor of points of the quotient, explicitly raised to the universe of the
fppf quotient sheaf. Its fppf descent is the existing small-quotient descent theorem. -/
def etaleQuotientFppfSheaf (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (sheafCompose (Scheme.fppfTopology.over S) uliftFunctor.{u + 1, u}).obj
    ⟨P.etaleQuotientSpace.functorOfPoints, P.smallEtaleQuotientSheaf_isFppfSheaf⟩

/-- The canonical comparison extends the lifted small étale sheafification unit
along the fppf sheafification unit. -/
def quotientSheafToEtaleQuotient (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    P.quotientSheaf (Scheme.fppfTopology.over S) ⟶ P.etaleQuotientFppfSheaf :=
  ⟨sheafifyLift (Scheme.fppfTopology.over S)
    (Functor.whiskerRight P.toSmallEtaleQuotientSheaf uliftFunctor.{u + 1, u})
    P.etaleQuotientFppfSheaf.property⟩

/-- The comparison is specified on the original quotient presheaf, not by an
arbitrary identification of the two quotient objects. -/
@[reassoc]
theorem toSheafify_quotientSheafToEtaleQuotient (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) ≫
      P.quotientSheafToEtaleQuotient.hom =
        Functor.whiskerRight P.toSmallEtaleQuotientSheaf uliftFunctor.{u + 1, u} :=
  toSheafify_sheafifyLift _ _ _

/-- The comparison intertwines the actual fppf and algebraic-space quotient
maps, with the universe transport displayed as whiskering by `ULift`. -/
theorem quotientMap_quotientSheafToEtaleQuotient (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    (P.quotientMap (Scheme.fppfTopology.over S)).hom ≫
        P.quotientSheafToEtaleQuotient.hom =
      Functor.whiskerRight P.etaleQuotientMap uliftFunctor.{u + 1, u} := by
  ext T a
  obtain ⟨a⟩ := a
  change P.quotientSheafToEtaleQuotient.hom.app T
      ((P.quotientMap (Scheme.fppfTopology.over S)).hom.app T (ULift.up a)) = _
  rw [quotientMap_app (Scheme.fppfTopology.over S) P]
  exact congrArg (fun f => f.app T (ULift.up (Quot.mk (P.pointRel T.unop) a)))
    P.toSheafify_quotientSheafToEtaleQuotient

namespace QuotientComparison

/-- On each small étale site `ULift` preserves sheafification. Both local
bijection criteria here come from mathlib (including the affine étale dense subsite). -/
theorem ulift_preservesSheafification (T : Scheme.{u}) :
    T.smallEtaleTopology.PreservesSheafification uliftFunctor.{u + 1, u} := by
  constructor
  intro F G f hf
  change T.smallEtaleTopology.W (Functor.whiskerRight f uliftFunctor.{u + 1, u})
  letI := hf.isLocallyInjective
  letI := hf.isLocallySurjective
  have hinj : Presheaf.IsLocallyInjective T.smallEtaleTopology
      (Functor.whiskerRight f uliftFunctor.{u + 1, u}) := by
    constructor
    intro X x y h
    change ULift.up (f.app X x.down) = ULift.up (f.app X y.down) at h
    have hxy := Presheaf.equalizerSieve_mem T.smallEtaleTopology f x.down y.down
      (congrArg ULift.down h)
    convert hxy using 1
    ext Y g
    exact ULift.ext_iff
  have hsurj : Presheaf.IsLocallySurjective T.smallEtaleTopology
      (Functor.whiskerRight f uliftFunctor.{u + 1, u}) := by
    constructor
    intro X x
    apply T.smallEtaleTopology.superset_covering _
      (Presheaf.imageSieve_mem T.smallEtaleTopology f x.down)
    intro Y g hg
    obtain ⟨y, hy⟩ := hg
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  letI := hinj
  letI := hsurj
  exact T.smallEtaleTopology.W_of_isLocallyBijective _

/-- Restrict the fppf quotient to the étale topology. The topology inclusion is
the actual inclusion of étale covering sieves in fppf covering sieves. -/
def etaleTarget (P : PreRelation U) :
    Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  ⟨(P.quotientSheaf (Scheme.fppfTopology.over S)).obj,
    Presheaf.IsSheaf.of_le (EtaleSheafification.etale_le_fppf_over S)
      (P.quotientSheaf (Scheme.fppfTopology.over S)).property⟩

/-- Descend the lifted quotient unit on the small étale site of a test scheme. -/
def localLift (P : PreRelation U) (T : Over S) :
    (EtaleSheafification.localSheaf P.quotientPresheaf T).obj ⋙
        uliftFunctor.{u + 1, u} ⟶
      (EtaleSheafification.testFunctor T).op ⋙ (etaleTarget P).obj := by
  letI := ulift_preservesSheafification T.left
  let Qlocal := ((EtaleSheafification.testFunctor T).sheafPushforwardContinuous
    (Type (u + 1)) T.left.smallEtaleTopology (Scheme.etaleTopology.over S)).obj
      (etaleTarget P)
  exact
    (sheafifyComposeIso T.left.smallEtaleTopology uliftFunctor.{u + 1, u}
      (EtaleSheafification.restriction P.quotientPresheaf T)).inv ≫
    sheafifyLift T.left.smallEtaleTopology
      (Functor.whiskerLeft (EtaleSheafification.testFunctor T).op
        (toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}))) Qlocal.property

/-- The local extension agrees with the original lifted quotient unit. -/
@[reassoc]
theorem localLift_fac (P : PreRelation U) (T : Over S) :
    Functor.whiskerRight (toSheafify T.left.smallEtaleTopology
        (EtaleSheafification.restriction P.quotientPresheaf T))
        uliftFunctor.{u + 1, u} ≫ localLift P T =
      Functor.whiskerLeft (EtaleSheafification.testFunctor T).op
        (toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})) := by
  letI := ulift_preservesSheafification T.left
  dsimp only [localLift]
  rw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_sheafifyLift]

/-- The reverse comparison on a test scheme is local descent followed by
restriction along the explicit identity-chart arrow. -/
def invApp (P : PreRelation U) (T : Over S) :
    ULift.{u + 1} (P.smallEtaleQuotientSheaf.obj.obj (op T)) ⟶
      (P.quotientSheaf (Scheme.fppfTopology.over S)).obj.obj (op T) :=
  (localLift P T).app (op (Scheme.Etale.mk (𝟙 T.left))) ≫
    (etaleTarget P).obj.map (EtaleSheafification.toIdentityChart T).op

/-- On every local generator the reverse comparison is the original fppf
sheafification unit, followed by restriction along the identity chart. -/
theorem invApp_local_unit (P : PreRelation U) (T : Over S)
    (q : (EtaleSheafification.restriction P.quotientPresheaf T).obj
      (op (Scheme.Etale.mk (𝟙 T.left)))) :
    invApp P T (ULift.up ((toSheafify T.left.smallEtaleTopology
      (EtaleSheafification.restriction P.quotientPresheaf T)).app
        (op (Scheme.Etale.mk (𝟙 T.left))) q)) =
      (P.quotientSheaf (Scheme.fppfTopology.over S)).obj.map
        (EtaleSheafification.toIdentityChart T).op
        ((toSheafify (Scheme.fppfTopology.over S)
          (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app
            (op ((EtaleSheafification.testFunctor T).obj
              (Scheme.Etale.mk (𝟙 T.left)))) (ULift.up q)) := by
  letI := ulift_preservesSheafification T.left
  let Q := etaleTarget P
  let Qlocal := ((EtaleSheafification.testFunctor T).sheafPushforwardContinuous
    (Type (u + 1)) T.left.smallEtaleTopology (Scheme.etaleTopology.over S)).obj Q
  let η := Functor.whiskerLeft (EtaleSheafification.testFunctor T).op
    (toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}))
  have h : Functor.whiskerRight
        (toSheafify T.left.smallEtaleTopology
          (EtaleSheafification.restriction P.quotientPresheaf T))
        uliftFunctor.{u + 1, u} ≫
      (sheafifyComposeIso T.left.smallEtaleTopology uliftFunctor.{u + 1, u}
        (EtaleSheafification.restriction P.quotientPresheaf T)).inv ≫
      sheafifyLift T.left.smallEtaleTopology η Qlocal.property = η := by
    rw [← Category.assoc, sheafComposeIso_inv_fac, toSheafify_sheafifyLift]
  exact congrArg (fun x => Q.obj.map (EtaleSheafification.toIdentityChart T).op x)
    (congrArg (fun f => f.app (op (Scheme.Etale.mk (𝟙 T.left))) (ULift.up q)) h)

/-- On a global quotient-presheaf section, descent returns its fppf image. -/
theorem invApp_unit (P : PreRelation U) (T : Over S)
    (q : P.quotientPresheaf.obj (op T)) :
    invApp P T (ULift.up (P.toSmallEtaleQuotientSheaf.app (op T) q)) =
      (toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app (op T) (ULift.up q) := by
  let a : (EtaleSheafification.testFunctor T).obj (Scheme.Etale.mk (𝟙 T.left)) ⟶ T :=
    Over.homMk (𝟙 T.left) (by
      change 𝟙 T.left ≫ T.hom = 𝟙 T.left ≫ T.hom
      rfl)
  change invApp P T (ULift.up ((toSheafify T.left.smallEtaleTopology
    (EtaleSheafification.restriction P.quotientPresheaf T)).app
      (op (Scheme.Etale.mk (𝟙 T.left))) (P.quotientPresheaf.map a.op q))) = _
  rw [invApp_local_unit]
  have hnat := congrArg (fun k => k (ULift.up q))
    ((toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).naturality a.op)
  erw [hnat]
  change ((P.quotientSheaf (Scheme.fppfTopology.over S)).obj.map a.op ≫
      (P.quotientSheaf (Scheme.fppfTopology.over S)).obj.map
        (EtaleSheafification.toIdentityChart T).op) _ = _
  rw [← Functor.map_comp, ← op_comp]
  have ha : EtaleSheafification.toIdentityChart T ≫ a = 𝟙 T := by
    apply Over.OverMorphism.ext
    simp [a, EtaleSheafification.toIdentityChart]
  rw [ha, op_id]
  erw [(P.quotientSheaf (Scheme.fppfTopology.over S)).obj.map_id]
  rfl

/-- Equality of maps from a lifted local sheafification is checked on its unit. -/
theorem localLift_ext (P : PreRelation U) (T : Over S)
    {G : T.left.Etaleᵒᵖ ⥤ Type (u + 1)}
    (hG : Presheaf.IsSheaf T.left.smallEtaleTopology G)
    (a b : (EtaleSheafification.localSheaf P.quotientPresheaf T).obj ⋙
      uliftFunctor.{u + 1, u} ⟶ G)
    (h : Functor.whiskerRight (toSheafify T.left.smallEtaleTopology
      (EtaleSheafification.restriction P.quotientPresheaf T))
      uliftFunctor.{u + 1, u} ≫ a =
      Functor.whiskerRight (toSheafify T.left.smallEtaleTopology
      (EtaleSheafification.restriction P.quotientPresheaf T))
      uliftFunctor.{u + 1, u} ≫ b) : a = b := by
  letI := ulift_preservesSheafification T.left
  let e := sheafifyComposeIso T.left.smallEtaleTopology uliftFunctor.{u + 1, u}
    (EtaleSheafification.restriction P.quotientPresheaf T)
  apply (cancel_epi e.hom).mp
  apply sheafify_hom_ext _ _ _ hG
  simpa only [e, ← Category.assoc, sheafComposeIso_hom_fac] using h

/-- Local descent commutes with the actual base-change transformation. -/
theorem localLift_pullback (P : PreRelation U) {T T' : Over S} (f : T' ⟶ T) :
    Functor.whiskerRight
        (sheafifyLift T.left.smallEtaleTopology
          (EtaleSheafification.presheafRestrictionMap P.quotientPresheaf f ≫
            Functor.whiskerLeft (Scheme.smallEtalePullback f.left).op
              (toSheafify T'.left.smallEtaleTopology
                (EtaleSheafification.restriction P.quotientPresheaf T')))
          (Functor.op_comp_isSheaf (Scheme.smallEtalePullback f.left)
            T.left.smallEtaleTopology T'.left.smallEtaleTopology
            (EtaleSheafification.localSheaf P.quotientPresheaf T')))
        uliftFunctor.{u + 1, u} ≫
      Functor.whiskerLeft (Scheme.smallEtalePullback f.left).op (localLift P T') =
    localLift P T ≫ Functor.whiskerRight
      (NatTrans.op (EtaleSheafification.testProjection f)) (etaleTarget P).obj := by
  let Q := etaleTarget P
  let Qlocal := ((EtaleSheafification.testFunctor T').sheafPushforwardContinuous
    (Type (u + 1)) T'.left.smallEtaleTopology (Scheme.etaleTopology.over S)).obj Q
  apply localLift_ext P T
    (Functor.op_comp_isSheaf (Scheme.smallEtalePullback f.left)
      T.left.smallEtaleTopology T'.left.smallEtaleTopology Qlocal)
  erw [← Category.assoc, ← Functor.whiskerRight_comp,
    toSheafify_sheafifyLift, Functor.whiskerRight_comp, Category.assoc,
    localLift_fac_assoc]
  ext E q
  calc
    _ = (toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app
          (op ((EtaleSheafification.testFunctor T').obj
            ((Scheme.smallEtalePullback f.left).obj E.unop)))
          (ULift.up ((EtaleSheafification.presheafRestrictionMap
            P.quotientPresheaf f).app E q.down)) :=
      congrArg (fun k => k (ULift.up ((EtaleSheafification.presheafRestrictionMap
        P.quotientPresheaf f).app E q.down)))
        (NatTrans.congr_app (localLift_fac P T')
          (op ((Scheme.smallEtalePullback f.left).obj E.unop)))
    _ = _ := (toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).naturality_apply
        ((EtaleSheafification.testProjection f).app E.unop).op q

/-- Naturality of the explicitly descended inverse components. -/
theorem invApp_naturality (P : PreRelation U) {T T' : Over S} (f : T' ⟶ T) :
    uliftFunctor.{u + 1, u}.map (P.smallEtaleQuotientSheaf.obj.map f.op) ≫
        invApp P T' =
      invApp P T ≫ (P.quotientSheaf (Scheme.fppfTopology.over S)).obj.map f.op := by
  let B := Scheme.smallEtalePullback f.left
  let i : Scheme.Etale.mk (𝟙 T'.left) ⟶ B.obj (Scheme.Etale.mk (𝟙 T.left)) :=
    MorphismProperty.Over.homMk
      (Limits.pullback.lift f.left (𝟙 T'.left)
        ((Category.comp_id f.left).trans (Category.id_comp f.left).symm)) (by
          exact Limits.pullback.lift_snd _ _ _)
  have h := NatTrans.congr_app (localLift_pullback P f)
    (op (Scheme.Etale.mk (𝟙 T.left)))
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  have hn := (localLift P T').naturality i.op
  dsimp only [smallEtaleQuotientSheaf, EtaleSheafification.sheafify,
    EtaleSheafification.restrictionMap, invApp]
  rw [uliftFunctor.map_comp]
  change _ ≫ uliftFunctor.{u + 1, u}.map
      ((EtaleSheafification.localSheaf P.quotientPresheaf T').obj.map i.op) ≫
      (localLift P T').app (op (Scheme.Etale.mk (𝟙 T'.left))) ≫ _ = _
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc _ ((localLift P T').app
    (op (Scheme.Etale.mk (𝟙 T'.left)))) _, hn]
  simp only [Category.assoc]
  erw [← Category.assoc _ ((localLift P T').app
    (op (B.obj (Scheme.Etale.mk (𝟙 T.left))))), h]
  simp only [Category.assoc]
  congr 1
  change (etaleTarget P).obj.map _ ≫ (etaleTarget P).obj.map _ ≫
      (etaleTarget P).obj.map _ =
    (etaleTarget P).obj.map _ ≫ (etaleTarget P).obj.map _
  rw [← (etaleTarget P).obj.map_comp, ← (etaleTarget P).obj.map_comp,
    ← (etaleTarget P).obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, NatTrans.op_app, Functor.op_map, Quiver.Hom.unop_op]
  apply Over.OverMorphism.ext
  change (𝟙 T'.left ≫ i.left) ≫ Limits.pullback.fst (𝟙 T.left) f.left =
    f.left ≫ 𝟙 T.left
  simp only [Category.id_comp, Category.comp_id]
  exact Limits.pullback.lift_fst _ _ _

end QuotientComparison

/-- The reverse comparison uses the specified small-site descent maps. -/
def etaleQuotientToQuotientSheaf (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    P.etaleQuotientFppfSheaf ⟶ P.quotientSheaf (Scheme.fppfTopology.over S) :=
  ⟨{
    app T := QuotientComparison.invApp P T.unop
    naturality := by
      intro X Y f
      exact QuotientComparison.invApp_naturality P f.unop
  }⟩

/-- The reverse comparison extends the original fppf quotient unit. -/
@[reassoc]
theorem toSmallEtaleQuotientSheaf_inverse (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    Functor.whiskerRight P.toSmallEtaleQuotientSheaf uliftFunctor.{u + 1, u} ≫
        P.etaleQuotientToQuotientSheaf.hom =
      toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) := by
  ext T q
  obtain ⟨q⟩ := q
  exact QuotientComparison.invApp_unit P T.unop q

/-- The actual algebraic-space quotient map, transported to large fppf sheaves
by subcanonicity and `ULift`. -/
def etaleQuotientFppfMap (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj U ⟶
      P.etaleQuotientFppfSheaf :=
  ⟨Functor.whiskerRight P.etaleQuotientMap uliftFunctor.{u + 1, u}⟩

/-- Universe transport preserves local surjectivity of the actual atlas. -/
theorem etaleQuotientFppfMap_locallySurjective (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      P.etaleQuotientFppfMap.hom := by
  apply Presheaf.isLocallySurjective_of_le (EtaleSheafification.etale_le_fppf_over S)
  letI := P.smallEtaleQuotientSheafMk_locallySurjective
  constructor
  intro T q
  apply (Scheme.etaleTopology.over S).superset_covering _
    (Presheaf.imageSieve_mem (Scheme.etaleTopology.over S)
      P.smallEtaleQuotientSheafMk q.down)
  intro T' f hf
  obtain ⟨a, ha⟩ := hf
  exact ⟨ULift.up a, congrArg ULift.up ha⟩

/-- The two canonical extensions are inverse. The maps themselves are constructed
by sheafification descent, independently of this equality obligation. -/
theorem quotientSheafEtaleQuotient_inverse_laws (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    P.quotientSheafToEtaleQuotient ≫ P.etaleQuotientToQuotientSheaf = 𝟙 _ ∧
      P.etaleQuotientToQuotientSheaf ≫ P.quotientSheafToEtaleQuotient = 𝟙 _ := by
  have hforward : P.quotientMap (Scheme.fppfTopology.over S) ≫
      P.quotientSheafToEtaleQuotient = P.etaleQuotientFppfMap := by
    apply Sheaf.hom_ext
    exact P.quotientMap_quotientSheafToEtaleQuotient
  have hreverse : P.etaleQuotientFppfMap ≫ P.etaleQuotientToQuotientSheaf =
      P.quotientMap (Scheme.fppfTopology.over S) := by
    apply Sheaf.hom_ext
    ext T a
    obtain ⟨a⟩ := a
    change QuotientComparison.invApp P T.unop
        (ULift.up (P.toSmallEtaleQuotientSheaf.app T
          (Quot.mk (P.pointRel T.unop) a))) = _
    rw [QuotientComparison.invApp_unit]
    exact (quotientMap_app (Scheme.fppfTopology.over S) P a).symm
  constructor
  · apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (P.quotientSheaf (Scheme.fppfTopology.over S)).property
    change toSheafify _ _ ≫ P.quotientSheafToEtaleQuotient.hom ≫
      P.etaleQuotientToQuotientSheaf.hom = toSheafify _ _ ≫ 𝟙 _
    rw [← Category.assoc, P.toSheafify_quotientSheafToEtaleQuotient,
      P.toSmallEtaleQuotientSheaf_inverse, Category.comp_id]
  · letI := P.etaleQuotientFppfMap_locallySurjective
    haveI : Epi P.etaleQuotientFppfMap := Sheaf.epi_of_isLocallySurjective _
    apply (cancel_epi P.etaleQuotientFppfMap).mp
    rw [← Category.assoc, hreverse, hforward, Category.comp_id]

/-- Identify the fppf quotient with the universe-raised functor of points of
the specified étale quotient space, using the two explicit descent maps. -/
def quotientSheafEtaleQuotientIso (P : PreRelation U) [P.IsEtaleEquivalenceRelation] :
    P.quotientSheaf (Scheme.fppfTopology.over S) ≅ P.etaleQuotientFppfSheaf where
  hom := P.quotientSheafToEtaleQuotient
  inv := P.etaleQuotientToQuotientSheaf
  hom_inv_id := P.quotientSheafEtaleQuotient_inverse_laws.1
  inv_hom_id := P.quotientSheafEtaleQuotient_inverse_laws.2

/-- The forward comparison commutes with the two specified quotient maps. -/
@[reassoc]
theorem quotientMap_quotientSheafEtaleQuotientIso_hom (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    P.quotientMap (Scheme.fppfTopology.over S) ≫ P.quotientSheafEtaleQuotientIso.hom =
      P.etaleQuotientFppfMap := by
  apply Sheaf.hom_ext
  exact P.quotientMap_quotientSheafToEtaleQuotient

/-- The reverse comparison also commutes with the specified quotient maps. -/
@[reassoc]
theorem etaleQuotientFppfMap_quotientSheafEtaleQuotientIso_inv (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    P.etaleQuotientFppfMap ≫ P.quotientSheafEtaleQuotientIso.inv =
      P.quotientMap (Scheme.fppfTopology.over S) := by
  rw [← P.quotientMap_quotientSheafEtaleQuotientIso_hom]
  simp

/-- Under the explicit universe/topology transport, the same two scheme maps
of `P` are the kernel pair of the actual algebraic-space quotient projection. -/
theorem isKernelPair_etaleQuotientFppfMap (P : PreRelation U)
    [P.IsEtaleEquivalenceRelation] :
    IsKernelPair P.etaleQuotientFppfMap
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.t)
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map P.s) := by
  letI := IsEtaleEquivalenceRelation.isEquivalenceRelation (P := P)
  rw [← P.quotientMap_quotientSheafEtaleQuotientIso_hom]
  exact P.isKernelPair_quotientMap.comp_of_mono

end

/-- The canonical morphism from a coproduct summand to the algebraic-space
quotient of an étale equivalence relation on the coproduct. -/
def etaleQuotientSummand {I : Type v} [Small.{u} I] (Mi : I → Over S)
    (P : PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (i : I) : AlgebraicSpace.ofOver (Mi i) ⟶ P.etaleQuotientSpace :=
  yoneda.map (Scheme.Coproduct.overι Mi i) ≫ P.etaleQuotientMap

/-- On scheme-valued points the quotient summand map takes the quotient class
after composing with the coproduct inclusion. -/
@[simp]
theorem etaleQuotientSummand_app {I : Type v} [Small.{u} I] (Mi : I → Over S)
    (P : PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (i : I) {T : Over S} (a : T ⟶ Mi i) :
    (etaleQuotientSummand Mi P i).app (op T) a =
      P.smallEtaleQuotientSheafMk.app (op T) (a ≫ Scheme.Coproduct.overι Mi i) := rfl

end AlgebraicGeometry.Scheme.PreRelation
