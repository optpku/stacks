module

public import stacks_project.Chap99.«99_7_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

/-!
# Space-level quotient points of a quasi-coherent module

This module extends the scheme-level quotient points of `Q_{F/X/B}` to an algebraic
space `T` over `S`, via a morphism `h : T ⟶ B` and a kernel-identified quotient of
the pullback of `F` to `X ×_{B,h} T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pullback `F_T` of a module `F` along the projection `X ×_{B,h} T ⟶ X`. -/
def spaceFiberF {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    (pullback f h).Modules :=
  (Modules.pullback (pullback.fst f h)).obj F

/-- The canonical map `X_{T'} ⟶ X_T` induced by a morphism `a : T' ⟶ T` over `B`. -/
def spaceFiberMap {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B) (a : T' ⟶ T) :
    pullback f (a ≫ h) ⟶ pullback f h :=
  pullback.map f (a ≫ h) f h (𝟙 X) a (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    (Category.comp_id (a ≫ h))

/-- The map `spaceFiberMap f h a` commutes with the projections to `X`. -/
theorem spaceFiberMap_fst {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceFiberMap f h a ≫ pullback.fst f h = pullback.fst f (a ≫ h) := sorry

/-- The map `spaceFiberMap f h a` commutes with the projections to the varying base. -/
theorem spaceFiberMap_snd {T T' : AlgebraicSpace S} (f : X ⟶ B) (h : T ⟶ B)
    (a : T' ⟶ T) :
    spaceFiberMap f h a ≫ pullback.snd f h = pullback.snd f (a ≫ h) ≫ a := sorry

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `X_{T'} ⟶ X_T`. -/
def spaceFiberFCompIso {T T' : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) (a : T' ⟶ T) :
    spaceFiberF f F (a ≫ h) ≅
      (Modules.pullback (spaceFiberMap f h a)).obj (spaceFiberF f F h) :=
  eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj F)
      ((pullback.lift_fst (pullback.fst f (a ≫ h) ≫ 𝟙 X)
          (pullback.snd f (a ≫ h) ≫ a)
          (((Category.assoc (pullback.fst f (a ≫ h)) (𝟙 X) f).trans
              (congrArg (fun k ↦ pullback.fst f (a ≫ h) ≫ k) (Category.id_comp f))).trans
            ((pullback.condition :
                pullback.fst f (a ≫ h) ≫ f =
                  pullback.snd f (a ≫ h) ≫ (a ≫ h)).trans
              (Category.assoc (pullback.snd f (a ≫ h)) a h).symm))).trans
        (Category.comp_id _)).symm) ≪≫
    (Modules.pullbackComp (spaceFiberMap f h a) (pullback.fst f h)).symm.app F

/-- A quasi-coherent quotient of `F_T` that is flat over an algebraic space `T`. -/
structure SpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) where
  /-- The target module sheaf of the quotient. -/
  module : (pullback f h).Modules
  /-- The quotient morphism from `F_T`. -/
  map : spaceFiberF f F h ⟶ module
  /-- The quotient morphism is an epimorphism. -/
  map_epi : Epi map
  /-- The target is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The target is flat over `T`. -/
  isFlat : Modules.flatOver module (pullback.snd f h)

namespace SpacePoint

/-- Construct a space-level quotient point from an epimorphism `F_T ⟶ Q` with `Q`
quasi-coherent and flat over `T`. -/
def ofEpi {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B)
    (module : (pullback f h).Modules) (map : spaceFiberF f F h ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f h)) : SpacePoint f F h where
  module := module
  map := map
  map_epi := map_epi
  isQuasicoherent := isQuasicoherent
  isFlat := isFlat

/-- A space-level quotient point is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
and flat over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) :
    Epi Q.map ∧ Q.module.IsQuasicoherent ∧
      Modules.flatOver Q.module (pullback.snd f h) := sorry

/-- Pull back a space-level quotient point along a morphism of algebraic spaces. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) (a : T' ⟶ T) : SpacePoint f F (a ≫ h) where
  module := (Modules.pullback (spaceFiberMap f h a)).obj Q.module
  map := (spaceFiberFCompIso f F h a).hom ≫
    (Modules.pullback (spaceFiberMap f h a)).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry
  isFlat := sorry

/-- The module of a pulled-back space-level point is the module pullback along
`spaceFiberMap`. -/
theorem pullback_module {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} (Q : SpacePoint f F h) (a : T' ⟶ T) :
    (Q.pullback a).module = (Modules.pullback (spaceFiberMap f h a)).obj Q.module := sorry

/-- Two space-level quotient points are identified when they have the same kernel. -/
def Rel {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q₁ Q₂ : SpacePoint f F h) : Prop :=
  kernelSubobject Q₁.map = kernelSubobject Q₂.map

/-- Kernel equality is an equivalence relation on space-level quotient points. -/
theorem rel_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) : Equivalence (@Rel _ _ _ T f F h) := sorry

/-- Kernel identification of space-level quotient points is equivalent to an isomorphism
of targets over `F_T`. -/
theorem rel_iso_iff {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q₁ Q₂ : SpacePoint f F h) :
    Rel Q₁ Q₂ ↔ ∃ e : Q₁.module ≅ Q₂.module, Q₁.map ≫ e.hom = Q₂.map := sorry

end SpacePoint

/-- View a scheme-level quotient point as a space-level quotient point along `σ.hom`. -/
def Point.toSpacePoint {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    (Q : Point f F σ) : SpacePoint f F σ.hom where
  module := Q.module
  map := Q.map
  map_epi := Q.map_epi
  isQuasicoherent := Q.isQuasicoherent
  isFlat := Q.isFlat

/-- The module of `Point.toSpacePoint Q` is the underlying module of `Q`. -/
theorem Point.toSpacePoint_module {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    (Q : Point f F σ) : Q.toSpacePoint.module = Q.module := sorry

/-- The quotient map of `Point.toSpacePoint Q` is the underlying map of `Q`. -/
theorem Point.toSpacePoint_map {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    (Q : Point f F σ) : Q.toSpacePoint.map = Q.map := sorry

/-- The setoid of space-level quotient points modulo kernel equality. -/
def spaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    Setoid (SpacePoint f F h) where
  r := SpacePoint.Rel
  iseqv := SpacePoint.rel_isEquivalence f F h

/-- Pullback preserves the relation of the space-level quotient setoid. -/
theorem spaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : SpacePoint f F h),
      (spaceSetoid f F h).r Q₁ Q₂ →
        (spaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) := sorry

/-- A pair `(h, Q)` consisting of a morphism `h : T ⟶ B` and a kernel-identified
quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure SpaceQuotient (f : X ⟶ B) (F : X.Modules) (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The kernel-identified quotient class of `F_T`. -/
  quotient : _root_.Quotient (spaceSetoid f F hom)

namespace SpaceQuotient

/-- Package a space-level quotient point over `h : T ⟶ B` as the pair `(h, [Q])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) : SpaceQuotient f F T where
  hom := h
  quotient := Quotient.mk (spaceSetoid f F h) Q

/-- Pull back a pair `(h, Q)` along `a : T' ⟶ T`, sending it to `(h ∘ a, a^* Q)`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : SpaceQuotient f F T) (a : T' ⟶ T) : SpaceQuotient f F T' where
  hom := a ≫ Q.hom
  quotient :=
    _root_.Quotient.map (fun P : SpacePoint f F Q.hom ↦ P.pullback a)
      (spaceSetoid_rel_pullback f F Q.hom a) Q.quotient

/-- The morphism of a pulled-back pair is the composite `a ≫ Q.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : SpaceQuotient f F T) (a : T' ⟶ T) :
    (Q.pullback a).hom = a ≫ Q.hom := sorry

end SpaceQuotient

/-- A finitely presented quasi-coherent quotient of `F_T` that is flat over an
algebraic space `T`. -/
structure FpSpacePoint {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) where
  /-- The underlying space-level quotient point. -/
  point : SpacePoint f F h
  /-- The target is of finite presentation. -/
  isFinitePresentation : point.module.IsFinitePresentation

namespace FpSpacePoint

/-- Construct an `FpSpacePoint` from an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent
of finite presentation and flat over `T`. -/
def ofEpi {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B)
    (module : (pullback f h).Modules) (map : spaceFiberF f F h ⟶ module)
    (map_epi : Epi map) (isQuasicoherent : module.IsQuasicoherent)
    (isFlat : Modules.flatOver module (pullback.snd f h))
    (isFinitePresentation : module.IsFinitePresentation) : FpSpacePoint f F h where
  point := SpacePoint.ofEpi f F h module map map_epi isQuasicoherent isFlat
  isFinitePresentation := isFinitePresentation

/-- Convert a space-level quotient point whose target is of finite presentation into an
`FpSpacePoint`. -/
def ofPoint {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : SpacePoint f F h) (isFinitePresentation : Q.module.IsFinitePresentation) :
    FpSpacePoint f F h where
  point := Q
  isFinitePresentation := isFinitePresentation

/-- The underlying space-level quotient point of a finitely presented quotient point. -/
abbrev toPoint {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : FpSpacePoint f F h) : SpacePoint f F h :=
  Q.point

/-- An `FpSpacePoint` is an epimorphism `F_T ⟶ Q` with `Q` quasi-coherent of finite
presentation and flat over `T`. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : FpSpacePoint f F h) :
    Epi Q.point.map ∧ Q.point.module.IsQuasicoherent ∧
      Q.point.module.IsFinitePresentation ∧
      Modules.flatOver Q.point.module (pullback.snd f h) := sorry

/-- Pull back a finitely presented space-level quotient point along a morphism of
algebraic spaces. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : FpSpacePoint f F h) (a : T' ⟶ T) : FpSpacePoint f F (a ≫ h) where
  point := Q.point.pullback a
  isFinitePresentation := sorry

/-- The module of a pulled-back `FpSpacePoint` is the module pullback along
`spaceFiberMap`. -/
theorem pullback_module {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    {h : T ⟶ B} (Q : FpSpacePoint f F h) (a : T' ⟶ T) :
    (Q.pullback a).point.module =
      (Modules.pullback (spaceFiberMap f h a)).obj Q.point.module := sorry

end FpSpacePoint

/-- Kernel identification is an equivalence relation on finitely presented space-level
quotient points. -/
theorem fpSpaceSetoid_isEquivalence {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    (h : T ⟶ B) :
    Equivalence (fun Q₁ Q₂ : FpSpacePoint f F h ↦ SpacePoint.Rel Q₁.point Q₂.point) :=
  sorry

/-- The setoid of finitely presented space-level quotient points modulo kernel equality. -/
def fpSpaceSetoid {T : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules) (h : T ⟶ B) :
    Setoid (FpSpacePoint f F h) where
  r Q₁ Q₂ := SpacePoint.Rel Q₁.point Q₂.point
  iseqv := fpSpaceSetoid_isEquivalence f F h

/-- Pullback preserves the relation of the finitely presented space-level quotient
setoid. -/
theorem fpSpaceSetoid_rel_pullback {T T' : AlgebraicSpace S} (f : X ⟶ B)
    (F : X.Modules) (h : T ⟶ B) (a : T' ⟶ T) :
    ∀ (Q₁ Q₂ : FpSpacePoint f F h),
      (fpSpaceSetoid f F h).r Q₁ Q₂ →
        (fpSpaceSetoid f F (a ≫ h)).r (Q₁.pullback a) (Q₂.pullback a) := sorry

/-- A pair `(h, Q)` consisting of a morphism `h : T ⟶ B` and a kernel-identified
finitely presented quasi-coherent quotient of `F_T` that is flat over `T`. -/
structure FpSpaceQuotient (f : X ⟶ B) (F : X.Modules) (T : AlgebraicSpace S) where
  /-- The morphism `h : T ⟶ B`. -/
  hom : T ⟶ B
  /-- The kernel-identified finitely presented quotient class of `F_T`. -/
  quotient : _root_.Quotient (fpSpaceSetoid f F hom)

namespace FpSpaceQuotient

/-- Package a finitely presented space-level quotient point over `h : T ⟶ B` as the
pair `(h, [Q])`. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules} {h : T ⟶ B}
    (Q : FpSpacePoint f F h) : FpSpaceQuotient f F T where
  hom := h
  quotient := Quotient.mk (fpSpaceSetoid f F h) Q

/-- Pull back a finitely presented pair `(h, Q)` along `a : T' ⟶ T`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : FpSpaceQuotient f F T) (a : T' ⟶ T) : FpSpaceQuotient f F T' where
  hom := a ≫ Q.hom
  quotient :=
    _root_.Quotient.map (fun P : FpSpacePoint f F Q.hom ↦ P.pullback a)
      (fpSpaceSetoid_rel_pullback f F Q.hom a) Q.quotient

/-- The morphism of a pulled-back finitely presented pair is the composite `a ≫ Q.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F : X.Modules}
    (Q : FpSpaceQuotient f F T) (a : T' ⟶ T) :
    (Q.pullback a).hom = a ≫ Q.hom := sorry

end FpSpaceQuotient

end AlgebraicGeometry.AlgebraicSpace.Quot
