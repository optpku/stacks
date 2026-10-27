/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.WeakIdealSystem

/-!
# Remark 87.13.3 (Weak ideals of definition)

Weak ideals, their quotient thickenings, and fundamental systems on McQuillan formal schemes.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/- The ideal of a quotient morphism is its actual structure-sheaf kernel. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.Hom.ker_ideal :
  ∀ {Y X : FormalScheme.{u}} (f : Y ⟶ X) (U : X.affineOpens),
    (Hom.ker f).ideal U =
      RingHom.ker ((Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val)

#check (AlgebraicGeometry.McQuillan.FormalScheme.IdealSheafData.ker_quotientι_eq :
  ∀ {X : FormalScheme.{u}} (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I),
    Hom.ker (I.quotientι hI) = I)

/- Weakness is the affinewise weak-ideal condition. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.isWeakIdealOfDefinition_iff :
  ∀ {X : FormalScheme.{u}} (I : IdealSheafData X),
    IsWeakIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U))

/- Weakness may be checked on an affine open cover. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.isWeakIdealOfDefinition_iff_affineCover :
  ∀ {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤),
    IsWeakIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal (𝒰 i)))

/- Weak ideals classify bounded scheme-source thickenings through their canonical quotients. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.weakIdeal_thickening_correspondence :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X : FormalScheme.{u}}
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size),
    (∀ (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I),
      IsAffineFormalAlgebraicSpace.isRelativeThickening (I.toSchemeThickening 𝒮 S hI)) ∧
    ∀ (Z : Scheme.{u})
      (hZ : ∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size)
      (i : (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z) ⟶ (sheafOfPoints 𝒮 S).obj X),
      IsAffineFormalAlgebraicSpace.isRelativeThickening i →
        ∃! I : IdealSheafData X, ∃ (hI : IsWeakIdealOfDefinition I)
          (e : I.quotientScheme hI ≅ Z),
          (sheafOfPoints 𝒮 S).map (ofScheme.map e.hom) ≫ i =
            I.toSchemeThickening 𝒮 S hI)

/- Fundamental systems are affinewise neighbourhood bases of weak ideals. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.isFundamentalSystem_iff :
  ∀ {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X),
    IsFundamentalSystem I ↔ ∀ U : X.affineOpens,
      TopologicalRing.IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U))

/- A nonempty downward-directed family is fundamental if and only if it is
fundamental on an affine open cover. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.isFundamentalSystem_iff_affineCover :
  ∀ {X : FormalScheme.{u}}
    {ι : Type u} (I : ι → IdealSheafData X)
    (hne : Nonempty ι)
    (hdir : ∀ i j : ι, ∃ k : ι, ∀ U : X.affineOpens,
      (I k).ideal U ≤ (I i).ideal U ∧ (I k).ideal U ≤ (I j).ideal U)
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤),
    IsFundamentalSystem I ↔
      ∀ j, IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal (𝒰 j)))

/- Existence may be checked on an affine open cover without assuming that the
supplied family is directed: finite-intersection refinement is permitted. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.exists_fundamentalSystem_iff_affineCover :
  ∀ {X : FormalScheme.{u}} {κ : Type u} (𝒰 : κ → X.affineOpens)
    (hcover : ⨆ j, (𝒰 j).1 = ⊤),
    Nonempty (FundamentalSystem X) ↔
      ∃ (ι : Type u) (I : ι → IdealSheafData X), Nonempty ι ∧
        ∀ j, TopologicalRing.IsFundamentalSystemOfWeakIdeals
          (fun i ↦ (I i).ideal (𝒰 j)))

/- Remark 87.13.3 (Weak ideals of definition)
The functor of points is a directed colimit of bounded schemes along thickenings
if and only if a fundamental system of weak ideals of definition exists. -/
@[stacks 0AIV] #check (AlgebraicGeometry.McQuillan.FormalScheme.exists_fundamentalSystem_iff_isDirectedColimit :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u})
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size),
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            (∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size) ∧
            Nonempty (D.obj i ≅ (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z)))

end AlgebraicGeometry.McQuillan.FormalScheme
