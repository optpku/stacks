/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Smooth algebraic-space presentation squares

A morphism of algebraic stacks may be tested on 2-commutative squares whose
vertices are algebraic spaces, whose vertical arrows are smooth, and whose
comparison into the 2-fibre product `TwoFibreProduct.apex f b` is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A 2-commutative square presenting a morphism of algebraic stacks by algebraic
spaces, with smooth vertical arrows. -/
def IsSmoothSpaceSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
    Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)

/-- A square is a smooth algebraic-space presentation square if and only if the
vertical arrows are smooth and the two paths `U.toGroupoids ⟶ Y` are
2-isomorphic. -/
theorem IsSmoothSpaceSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsSmoothSpaceSquare f a b h ↔
      Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
        Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  sorry

/-- Smooth vertical arrows and a 2-isomorphism of paths yield a smooth
algebraic-space presentation square. -/
theorem IsSmoothSpaceSquare.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (ha : Groupoids.Hom.Smooth a)
    (hb : Groupoids.Hom.Smooth b)
    (hsq : Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b)) :
    IsSmoothSpaceSquare f a b h :=
  sorry

/-- A smooth algebraic-space presentation square has smooth vertical arrows and
a 2-isomorphism of the two paths `U.toGroupoids ⟶ Y`. -/
theorem IsSmoothSpaceSquare.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hsq : IsSmoothSpaceSquare f a b h) :
    Groupoids.Hom.Smooth a ∧ Groupoids.Hom.Smooth b ∧
      Nonempty (a ≫ f ≅ AlgebraicSpace.toGroupoids.map h ≫ b) :=
  sorry

/-- The comparison `U ⟶ X ×_Y V` is smooth: some 1-morphism to the chosen
2-fibre product `TwoFibreProduct.apex f b` is smooth and 2-isomorphic to the
given legs `a` and `toGroupoids.map h`. -/
def HasSmoothComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
    Groupoids.Hom.Smooth φ ∧
      Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
        Nonempty
          (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
            AlgebraicSpace.toGroupoids.map h)

/-- Smooth comparison into `TwoFibreProduct.apex f b` means some smooth 1-morphism
is 2-isomorphic to the given legs. -/
theorem HasSmoothComparison.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    HasSmoothComparison f a b h ↔
      ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
        Groupoids.Hom.Smooth φ ∧
          Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
            Nonempty
              (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
                AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- A smooth comparison 1-morphism into `TwoFibreProduct.apex f b` witnesses
`HasSmoothComparison`. -/
theorem HasSmoothComparison.of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b)
    (hφ : Groupoids.Hom.Smooth φ)
    (hfst : Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a))
    (hsnd : Nonempty
      (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
        AlgebraicSpace.toGroupoids.map h)) :
    HasSmoothComparison f a b h :=
  sorry

/-- A smooth comparison supplies a 1-morphism `φ` to `TwoFibreProduct.apex f b`
that is smooth and 2-isomorphic to the given legs. -/
theorem HasSmoothComparison.spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} {f : X ⟶ Y} {a : U.toGroupoids ⟶ X}
    {b : V.toGroupoids ⟶ Y} {h : U ⟶ V} (hφ : HasSmoothComparison f a b h) :
    ∃ φ : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f b,
      Groupoids.Hom.Smooth φ ∧
        Nonempty (φ ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f b ≅ a) ∧
          Nonempty
            (φ ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f b ≅
              AlgebraicSpace.toGroupoids.map h) :=
  sorry

/-- A smooth algebraic-space presentation square whose source atlas is
surjective. -/
def IsSmoothSurjectivePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {U V : AlgebraicSpace S} (f : X ⟶ Y) (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) : Prop :=
  IsSmoothSpaceSquare f a b h ∧ Groupoids.Hom.Surjective a

/-- A square is a smooth surjective presentation if and only if it is a smooth
algebraic-space square whose source atlas is surjective. -/
theorem IsSmoothSurjectivePresentation.iff {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} (f : X ⟶ Y)
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V) :
    IsSmoothSurjectivePresentation f a b h ↔
      IsSmoothSpaceSquare f a b h ∧ Groupoids.Hom.Surjective a :=
  sorry

/-- A smooth algebraic-space square with surjective source atlas is a smooth
surjective presentation. -/
theorem IsSmoothSurjectivePresentation.of {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hsq : IsSmoothSpaceSquare f a b h) (ha : Groupoids.Hom.Surjective a) :
    IsSmoothSurjectivePresentation f a b h :=
  sorry

/-- A smooth surjective presentation is a smooth algebraic-space square with
surjective source atlas. -/
theorem IsSmoothSurjectivePresentation.spec {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {U V : AlgebraicSpace S} {f : X ⟶ Y}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsSmoothSurjectivePresentation f a b h) :
    IsSmoothSpaceSquare f a b h ∧ Groupoids.Hom.Surjective a :=
  sorry

/-- Every 2-commutative algebraic-space square over `f` with smooth vertical
arrows and smooth comparison into `TwoFibreProduct.apex f b` has `P` on the top
arrow. -/
def forallSmoothComparison {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V),
    IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h

/-- `forallSmoothComparison P f` means `P` holds on the top arrow of every smooth
algebraic-space square over `f` with smooth comparison. -/
theorem forallSmoothComparison.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    forallSmoothComparison P f ↔
      ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V),
        IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h :=
  sorry

/-- The universal checking condition yields `forallSmoothComparison`. -/
theorem forallSmoothComparison.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y}
    (hP : ∀ {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsSmoothSpaceSquare f a b h → HasSmoothComparison f a b h → P h) :
    forallSmoothComparison P f :=
  sorry

/-- Under `forallSmoothComparison`, the top arrow of a smooth algebraic-space
square with smooth comparison has `P`. -/
theorem forallSmoothComparison.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : forallSmoothComparison P f) {U V : AlgebraicSpace S}
    (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hsq : IsSmoothSpaceSquare f a b h) (hφ : HasSmoothComparison f a b h) :
    P h :=
  sorry

/-- Some smooth algebraic-space square over `f` with surjective source atlas has
`P` on the top arrow. -/
def existsSurjectiveSmoothSquare {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
    (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h

/-- `existsSurjectiveSmoothSquare P f` is the existence of a smooth surjective
algebraic-space presentation whose top arrow has `P`. -/
theorem existsSurjectiveSmoothSquare.iff {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    existsSurjectiveSmoothSquare P f ↔
      ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
        (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

/-- A smooth surjective presentation whose top arrow has `P` witnesses
`existsSurjectiveSmoothSquare`. -/
theorem existsSurjectiveSmoothSquare.of {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} {U V : AlgebraicSpace S} (a : U.toGroupoids ⟶ X)
    (b : V.toGroupoids ⟶ Y) (h : U ⟶ V)
    (hpres : IsSmoothSurjectivePresentation f a b h) (hP : P h) :
    existsSurjectiveSmoothSquare P f :=
  sorry

/-- A witness of `existsSurjectiveSmoothSquare` supplies a smooth surjective
presentation whose top arrow has `P`. -/
theorem existsSurjectiveSmoothSquare.spec {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : existsSurjectiveSmoothSquare P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

end AlgebraicGeometry.AlgebraicStack
