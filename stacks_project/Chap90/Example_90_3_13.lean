/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.PowerSeries
import StacksCheckRecall

/-!
# A small essential surjection whose ordinary cotangent map is not an isomorphism

With `Λ = PowerSeries k`, `A = k` and `B = Λ ⧸ (X ^ 2)`, the residue map
`B ⟶ A` is a small extension with no section over `Λ`, hence an essential surjection.
The ordinary cotangent space of `B` is identified with `k` by the class of `X`.
The target cotangent space vanishes: the existing field criterion
`IsLocalRing.subsingleton_cotangentSpace_iff` applies to `k`.
Thus ordinary cotangent bijectivity fails, while relative cotangent bijectivity holds.
-/

open CategoryTheory IsLocalRing ArtinianLocalAlgCat

universe u

/- Example 90.3.13: the square-zero power-series quotient has an essential residue surjection. -/
@[stacks 06SA] #check (ArtinianLocalAlgCat.instIsEssentialSurjection_modXSqToResidue :
  ∀ (k : Type u) [Field k], IsEssentialSurjection (modXSqToResidue k))

#check (ArtinianLocalAlgCat.instIsSmallExtension_modXSqToResidue :
  ∀ (k : Type u) [Field k], IsSmallExtension (modXSqToResidue k))

#check (ArtinianLocalAlgCat.not_exists_section_modXSqToResidue :
  ∀ (k : Type u) [Field k],
    ¬ ∃ s : residue (PowerSeries k) k ⟶ modXSq k, s ≫ modXSqToResidue k = 𝟙 _)

#check (ArtinianLocalAlgCat.not_bijective_mapAlgHom_modXSqToResidue :
  ∀ (k : Type u) [Field k],
    ¬ Function.Bijective (CotangentSpace.mapAlgHom (modXSqToResidue k).hom))

#check (ArtinianLocalAlgCat.bijective_mapRelative_modXSqToResidue :
  ∀ (k : Type u) [Field k], Function.Bijective (Hom.mapRelative (modXSqToResidue k)))

#check (ArtinianLocalAlgCat.cotangentSpaceModXSqEquiv :
  ∀ (k : Type u) [Field k],
    k ≃ₗ[k] CotangentSpace (PowerSeries k ⧸ PowerSeries.xSqIdeal k))
