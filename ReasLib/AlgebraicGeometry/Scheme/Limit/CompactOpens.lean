/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A compact open of the limit of a directed inverse system of qcqs schemes with affine
transition maps is the inverse image of a compact open at some stage. -/
theorem exists_compactOpen_preimage_eq {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (V : CompactOpens c.pt) :
    ∃ i : I, ∃ Vi : CompactOpens (D.obj i), c.π.app i ⁻¹ᵁ Vi.toOpens = V.toOpens := sorry

/-- Compact opens at two stages of a directed inverse system whose inverse images in the limit
agree have equal inverse images at some common upper stage. -/
theorem exists_compactOpen_common_refinement {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i i' : I) (Vi : CompactOpens (D.obj i)) (Vi' : CompactOpens (D.obj i'))
    (hpreimage : c.π.app i ⁻¹ᵁ Vi.toOpens = c.π.app i' ⁻¹ᵁ Vi'.toOpens) :
    ∃ (i'' : I) (hii'' : i ≤ i'') (hi'i'' : i' ≤ i''),
      D.map (homOfLE hii'') ⁻¹ᵁ Vi.toOpens =
        D.map (homOfLE hi'i'') ⁻¹ᵁ Vi'.toOpens := sorry

/-- A finite family of compact opens at one stage of a directed inverse system that covers the
limit after inverse image covers some upper stage after inverse image. -/
theorem exists_stage_of_compactOpen_cover {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (n : ℕ) (i : I) (Vi : Fin n → CompactOpens (D.obj i))
    (hcover : iSup (fun a ↦ c.π.app i ⁻¹ᵁ (Vi a).toOpens) = ⊤) :
    ∃ (i' : I) (hii' : i ≤ i'),
      iSup (fun a ↦ D.map (homOfLE hii') ⁻¹ᵁ (Vi a).toOpens) = ⊤ := sorry

end AlgebraicGeometry.Scheme.Limit
