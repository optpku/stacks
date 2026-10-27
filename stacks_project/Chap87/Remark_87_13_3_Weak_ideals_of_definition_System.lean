/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.WeakIdealSystem

/-!
# Fundamental systems of weak ideals of definition

The canonical formal-scheme API supplies explicit fundamental systems and their local criteria.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

#check (AlgebraicGeometry.McQuillan.FormalScheme.FundamentalSystem.ofFamily :
  ∀ {X : FormalScheme.{u}} {ι : Type u} (I : ι → IdealSheafData X),
    IsFundamentalSystem I → FundamentalSystem X)

#check (AlgebraicGeometry.McQuillan.FormalScheme.isFundamentalSystem_iff :
  ∀ {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X),
    IsFundamentalSystem I ↔ ∀ U : X.affineOpens,
      TopologicalRing.IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U))

#check (AlgebraicGeometry.McQuillan.FormalScheme.isFundamentalSystem_iff_affineCover :
  ∀ {X : FormalScheme.{u}}
    {ι : Type u} (I : ι → IdealSheafData X)
    (hne : Nonempty ι)
    (hdir : ∀ i j : ι, ∃ k : ι, ∀ U : X.affineOpens,
      (I k).ideal U ≤ (I i).ideal U ∧ (I k).ideal U ≤ (I j).ideal U)
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤),
    IsFundamentalSystem I ↔
      ∀ j, IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal (𝒰 j)))

#check (AlgebraicGeometry.McQuillan.FormalScheme.exists_fundamentalSystem_iff_isDirectedColimit :
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
