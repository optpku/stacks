/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Flat

/-!
# Flat morphisms in finite-type approximation systems

Flat morphisms of finite presentation between the limits of finite-type approximation systems
descend on a sufficiently late common tail, where their stage squares are cartesian.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The category of indices in the tail of a preorder above `i₀`, viewed inside the order-dual
index category used by inverse systems. -/
abbrev TailIndexCategory {I : Type u} [Preorder I] (i₀ : I) : Type u :=
  let j : OrderDual I := i₀
  Over j

namespace InverseSystemMorphismOverBase

/-- The flatness and cartesian base-change conditions at and beyond a fixed stage of a morphism
between inverse systems. -/
structure FlatBaseChangeAt
    {I : Type u} [Preorder I] {i₀ i₃ : I}
    {D : OrderDual I ⥤ Scheme.{u}}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃)
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) : Prop where
  /-- Every morphism at a stage beyond the fixed stage is flat. -/
  flat_stage : ∀ (i : I) (hi₃i : i₃ ≤ i),
    Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
  /-- Every later stage is obtained from the fixed stage by the corresponding cartesian square. -/
  stage_isPullback : ∀ (i : I) (hi₃i : i₃ ≤ i),
    IsPullback
      (Xsys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
      (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (Ysys.map (Over.homMk (homOfLE hi₃i) :
        tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
  /-- The limit square over the fixed stage is cartesian. -/
  limit_isPullback :
    IsPullback
      (xCone.π.app (tailObject i₃ hi₀i₃))
      f
      (φ.hom.app (tailObject i₃ hi₀i₃))
      (yCone.π.app (tailObject i₃ hi₀i₃))

namespace FlatBaseChangeAt

/-- Assemble the flatness and cartesian base-change conditions at a fixed stage. -/
def ofConditions
    {I : Type u} [Preorder I] {i₀ i₃ : I}
    {D : OrderDual I ⥤ Scheme.{u}}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃)
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt)
    (flat_stage : ∀ (i : I) (hi₃i : i₃ ≤ i),
      Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))))
    (stage_isPullback : ∀ (i : I) (hi₃i : i₃ ≤ i),
      IsPullback
        (Xsys.map (Over.homMk (homOfLE hi₃i) :
          tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
        (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (Ysys.map (Over.homMk (homOfLE hi₃i) :
          tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃)))
    (limit_isPullback :
      IsPullback
        (xCone.π.app (tailObject i₃ hi₀i₃))
        f
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (yCone.π.app (tailObject i₃ hi₀i₃))) :
    FlatBaseChangeAt hi₀i₃ xCone yCone φ f where
  flat_stage := flat_stage
  stage_isPullback := stage_isPullback
  limit_isPullback := limit_isPullback

end FlatBaseChangeAt

/-- The fixed-stage flat base-change certificate is equivalent to its three defining
conditions. -/
theorem flatBaseChangeAt_iff
    {I : Type u} [Preorder I] {i₀ i₃ : I}
    {D : OrderDual I ⥤ Scheme.{u}}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i₀}
    {yToBase : Ysys ⟶ tailBaseDiagram D i₀}
    (hi₀i₃ : i₀ ≤ i₃)
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) :
    FlatBaseChangeAt hi₀i₃ xCone yCone φ f ↔
      (∀ (i : I) (hi₃i : i₃ ≤ i),
        Flat (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))) ∧
      (∀ (i : I) (hi₃i : i₃ ≤ i),
        IsPullback
          (Xsys.map (Over.homMk (homOfLE hi₃i) :
            tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))
          (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i)))
          (φ.hom.app (tailObject i₃ hi₀i₃))
          (Ysys.map (Over.homMk (homOfLE hi₃i) :
            tailObject i (le_trans hi₀i₃ hi₃i) ⟶ tailObject i₃ hi₀i₃))) ∧
      IsPullback
        (xCone.π.app (tailObject i₃ hi₀i₃))
        f
        (φ.hom.app (tailObject i₃ hi₀i₃))
        (yCone.π.app (tailObject i₃ hi₀i₃)) := sorry

end InverseSystemMorphismOverBase

namespace FinitePresentationApproximationLimitSystem

/-- A flat morphism of finite presentation between the limits of finite-presentation
approximation systems is flat on a sufficiently late tail, and both its later-stage squares and
its limit square over the chosen stage are cartesian. -/
@[stacks 0CNT]
theorem exists_flatBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₀ : I}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₀)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₀)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : TailIndexCategory i₀,
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : TailIndexCategory i₀,
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [QuasiCompact xToS] [LocallyOfFiniteType xToS]
    [QuasiSeparated yToS] [QuasiCompact yToS] [LocallyOfFiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₀ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₀ Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hf_limit : φ.IsLimitMorphism xCone yCone f)
    (hflat : Flat f) (hfp : Scheme.Hom.FinitePresentation f) :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃),
      φ.FlatBaseChangeAt hi₀i₃ xCone yCone f := sorry

end FinitePresentationApproximationLimitSystem

namespace FiniteTypeApproximationDiagram

/-- A flat morphism of finite presentation between affine schemes is obtained by base change
from a flat finite-type morphism between affine schemes over `Spec ℤ`. -/
theorem exists_isPullback_of_flat
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [Flat f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (_ : Flat D.toSi),
      IsPullback D.toW f D.toSi π := sorry

end FiniteTypeApproximationDiagram

end AlgebraicGeometry
