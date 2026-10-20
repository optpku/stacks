/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basis-indexed gluing of schemes

This module describes relative scheme data indexed by a basis of open subsets
of a base scheme, together with equipped global realizations and compatible
isomorphisms between them.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Basis-indexed local scheme data over `S`, with transition morphisms along inclusions of basis
opens, pullback compatibility, and the cocycle condition. -/
@[stacks 01LH]
structure BasisSchemeGluing (S : Scheme.{u}) where
  /-- The index type for the selected basis family. -/
  ι : Type v
  /-- The basis open associated to each index. -/
  U : ι → S.Opens
  /-- The chosen family of opens is a basis for the topology on `S`. -/
  isBasis : TopologicalSpace.Opens.IsBasis (Set.range U)
  /-- The local scheme over the basis open `U i`. -/
  X : ι → Scheme.{u}
  /-- The structure morphism from the local piece to its basis open. -/
  f : ∀ i, X i ⟶ (U i).toScheme
  /-- The transition morphism attached to an inclusion `U i ≤ U j`. -/
  rho : ∀ ⦃i j : ι⦄, U i ≤ U j → (X i ⟶ X j)
  /-- Each transition realizes `X i` as the pullback of `X j` over the inclusion of basis opens. -/
  isPullback_rho : ∀ ⦃i j : ι⦄ (hij : U i ≤ U j),
      IsPullback (rho hij) (f i) (f j) (S.homOfLE hij)
  /-- Transitions compose along nested inclusions. -/
  cocycle : ∀ ⦃i j k : ι⦄ (hij : U i ≤ U j) (hjk : U j ≤ U k),
      rho (hij.trans hjk) = rho hij ≫ rho hjk

namespace BasisSchemeGluing

variable {S : Scheme.{u}} (D : BasisSchemeGluing S)

/-- The structure morphism from the local scheme `D.X i` to the ambient base scheme `S`. -/
def localToBase (i : D.ι) : D.X i ⟶ S :=
  D.f i ≫ (D.U i).ι

/-- A morphism `f : X ⟶ S` realizes `D` when its restrictions to the basis opens are identified
with the prescribed local schemes, compatibly with all transition morphisms. -/
@[stacks 01LH]
def Realizes {X : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ iScheme : ∀ i : D.ι, (f ⁻¹ᵁ D.U i).toScheme ≅ D.X i,
    (∀ i : D.ι, (iScheme i).hom ≫ D.f i = f ∣_ D.U i) ∧
      ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
        (iScheme i).inv ≫ X.homOfLE (f.preimage_mono hij) ≫ (iScheme j).hom =
          D.rho hij

/-- An equipped realization of `D`, including the chosen global scheme, its morphism to `S`,
and compatible identifications of all basis-open restrictions with the prescribed local schemes. -/
structure Realization where
  /-- The scheme obtained by gluing the local schemes. -/
  Y : Scheme.{u}
  /-- The glued scheme's structure morphism to the base scheme. -/
  toBase : Y ⟶ S
  /-- The chosen identification of each basis-open restriction with its prescribed local scheme. -/
  localIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i
  /-- Each chosen local identification is a morphism over its basis open. -/
  localIso_hom_over : ∀ i : D.ι, (localIso i).hom ≫ D.f i = toBase ∣_ D.U i
  /-- The chosen local identifications recover the prescribed transition morphisms. -/
  localTransition : ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
    (localIso i).inv ≫ Y.homOfLE (toBase.preimage_mono hij) ≫ (localIso j).hom = D.rho hij

/-- Forgetting the equipped fields shows that the underlying global morphism realizes the datum. -/
def Realization.realizes (R : D.Realization) : D.Realizes R.toBase :=
  ⟨R.localIso, R.localIso_hom_over, R.localTransition⟩

/-- An isomorphism between equipped realizations, including its restrictions to all basis opens
and compatibility with both the ambient inclusions and the chosen local identifications. -/
structure RealizationIso (R R' : D.Realization) where
  /-- The global isomorphism between the realized schemes. -/
  iso : R.Y ≅ R'.Y
  /-- The global isomorphism is over the base scheme `S`. -/
  hom_over : iso.hom ≫ R'.toBase = R.toBase
  /-- The chosen restriction of the global isomorphism to each basis-open preimage. -/
  localIso : ∀ i : D.ι,
    (R.toBase ⁻¹ᵁ D.U i).toScheme ≅ (R'.toBase ⁻¹ᵁ D.U i).toScheme
  /-- Each local restriction agrees with the global isomorphism after the open inclusions. -/
  localIso_hom_ι : ∀ i : D.ι,
    (localIso i).hom ≫ (R'.toBase ⁻¹ᵁ D.U i).ι =
      (R.toBase ⁻¹ᵁ D.U i).ι ≫ iso.hom
  /-- Each local restriction intertwines the two chosen identifications with the prescribed piece. -/
  localIso_hom_localIso : ∀ i : D.ι,
    (localIso i).hom ≫ (R'.localIso i).hom = (R.localIso i).hom

namespace RealizationIso

/-- The underlying global morphism of an isomorphism between equipped realizations. -/
def hom {D : BasisSchemeGluing S} {R R' : D.Realization} (e : D.RealizationIso R R') :
    R.Y ⟶ R'.Y :=
  e.iso.hom

end RealizationIso

namespace Realization

/-- A pullback-compatible basis-indexed scheme gluing datum admits an equipped realization over
`S`. -/
@[stacks 01LH]
theorem nonempty (D : BasisSchemeGluing S) : Nonempty D.Realization := sorry

/-- Between any two equipped realizations there is a unique isomorphism over `S` that intertwines
their chosen local identifications. -/
@[stacks 01LH]
theorem existsUniqueIso (R R' : D.Realization) :
    ∃ e : D.RealizationIso R R', ∀ e' : D.RealizationIso R R', e' = e := sorry

end Realization

end BasisSchemeGluing

end AlgebraicGeometry.Scheme
