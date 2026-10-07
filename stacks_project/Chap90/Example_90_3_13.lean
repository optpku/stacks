module

public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Definition_90_3_9
public import stacks_project.Chap90.Example_90_3_13_Quotient
public import stacks_project.Chap90.Lemma_90_3_5_Cotangent

/-!
# A small essential surjection whose ordinary cotangent map is not an isomorphism

With `Λ = PowerSeries k`, `A = k` and `B = Λ ⧸ (X ^ 2)`, the residue map
`B ⟶ A` is a small extension with no section in `ArtinianLocalAlgCat Λ k`, hence an
essential surjection. The induced map of ordinary cotangent spaces is not an
isomorphism, so the criterion of Lemma 90.3.12 (3) uses the relative cotangent map.
-/

@[expose] public section

open CategoryTheory IsLocalRing ArtinianLocalAlgCat

universe u

/-- Example 90.3.13 (1): with `Λ = PowerSeries k` and `B = Λ ⧸ (X ^ 2)`, the residue
map `modXSqToResidue k : B ⟶ A` in `ArtinianLocalAlgCat Λ k` is a small extension. -/
@[stacks 06SA, instance]
instance instIsSmallExtension_modXSqToResidue (k : Type u) [Field k] :
    IsSmallExtension (modXSqToResidue k) := sorry

/-- Example 90.3.13 (2): the residue map `modXSqToResidue k` has no right inverse in
`ArtinianLocalAlgCat (PowerSeries k) k`. -/
@[stacks 06SA]
theorem not_exists_section_modXSqToResidue (k : Type u) [Field k] :
    ¬ ∃ s : residue (PowerSeries k) k ⟶ modXSq k, s ≫ modXSqToResidue k = 𝟙 _ := sorry

/-- Example 90.3.13 (3): `modXSqToResidue k` is an essential surjection, by
Lemma 90.3.12, since it is a small extension with no right inverse in
`ArtinianLocalAlgCat (PowerSeries k) k`. -/
@[stacks 06SA, instance]
instance instIsEssentialSurjection_modXSqToResidue (k : Type u) [Field k] :
    IsEssentialSurjection (modXSqToResidue k) := sorry

/-- Example 90.3.13 (4): the ordinary cotangent map
`k ≅ m_B ⧸ m_B ^ 2 ⟶ m_A ⧸ m_A ^ 2 = 0` induced by `modXSqToResidue k` is not an
isomorphism. -/
@[stacks 06SA]
theorem not_bijective_mapAlgHom_modXSqToResidue (k : Type u) [Field k] :
    ¬ Function.Bijective (CotangentSpace.mapAlgHom (modXSqToResidue k).hom) := sorry

/-- Example 90.3.13 (5): the relative cotangent map
`m_B ⧸ (m_Λ B + m_B ^ 2) ⟶ m_A ⧸ (m_Λ A + m_A ^ 2)` of Lemma 90.3.12 (3) induced by
`modXSqToResidue k` is an isomorphism. -/
@[stacks 06SA]
theorem bijective_mapRelative_modXSqToResidue (k : Type u) [Field k] :
    Function.Bijective (Hom.mapRelative (modXSqToResidue k)) := sorry
