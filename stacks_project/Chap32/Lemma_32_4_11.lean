module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.CompactOpens
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 32.4.11 (1): compact opens of the limit descend to a stage. -/
@[stacks 01Z4] #check
  (AlgebraicGeometry.Scheme.Limit.exists_compactOpen_preimage_eq :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (V : CompactOpens c.pt),
      ∃ i : I, ∃ Vi : CompactOpens (D.obj i),
        c.π.app i ⁻¹ᵁ Vi.toOpens = V.toOpens)

/- Lemma 32.4.11 (2): equal inverse images of compact opens become equal at a common upper
stage. -/
@[stacks 01Z4] #check
  (AlgebraicGeometry.Scheme.Limit.exists_compactOpen_common_refinement :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i i' : I) (Vi : CompactOpens (D.obj i)) (Vi' : CompactOpens (D.obj i')),
      c.π.app i ⁻¹ᵁ Vi.toOpens = c.π.app i' ⁻¹ᵁ Vi'.toOpens →
        ∃ (i'' : I) (hii'' : i ≤ i'') (hi'i'' : i' ≤ i''),
          D.map (homOfLE hii'') ⁻¹ᵁ Vi.toOpens =
            D.map (homOfLE hi'i'') ⁻¹ᵁ Vi'.toOpens)

/- Lemma 32.4.11 (3): a finite family of compact opens covering the limit eventually covers an
upper stage. -/
@[stacks 01Z4] #check
  (AlgebraicGeometry.Scheme.Limit.exists_stage_of_compactOpen_cover :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (n : ℕ) (i : I) (Vi : Fin n → CompactOpens (D.obj i)),
      iSup (fun a ↦ c.π.app i ⁻¹ᵁ (Vi a).toOpens) = ⊤ →
        ∃ (i' : I) (hii' : i ≤ i'),
          iSup (fun a ↦ D.map (homOfLE hii') ⁻¹ᵁ (Vi a).toOpens) = ⊤)
