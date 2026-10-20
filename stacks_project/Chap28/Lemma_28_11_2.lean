/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Catenary
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u v

variable (S : Scheme.{u})

/- Lemma 28.11.2: catenarity of a scheme is equivalent to catenarity on an open cover, on every
affine-open section ring, or on the section rings of one affine open cover. -/
@[stacks 02IX] #check (AlgebraicGeometry.Scheme.catenarySpace_tfae S :
  List.TFAE
    [ CatenarySpace S,
      ∃ (ι : Type v) (U : ι → S.Opens), IsOpenCover U ∧ ∀ i, CatenarySpace (U i),
      ∀ U : S.affineOpens, IsCatenaryRing Γ(S, U),
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsCatenaryRing Γ(S, (𝒰.f i).opensRange) ])

#check (TopologicalSpace.catenarySpace_iff_hasOpenCoverByCatenarySpaces :
  CatenarySpace S ↔
    ∃ (ι : Type v) (U : ι → S.Opens), IsOpenCover U ∧ ∀ i, CatenarySpace (U i))

#check (AlgebraicGeometry.Scheme.catenarySpace_iff_forall_affineOpen_isCatenaryRing S :
  CatenarySpace S ↔ ∀ U : S.affineOpens, IsCatenaryRing Γ(S, U))

#check (AlgebraicGeometry.Scheme.catenarySpace_iff_exists_affineOpenCover_isCatenaryRing S :
  CatenarySpace S ↔
    ∃ 𝒰 : S.AffineOpenCover,
      ∀ i : 𝒰.I₀, IsCatenaryRing Γ(S, (𝒰.f i).opensRange))

/- Moreover, an immersion presents a locally closed subscheme, and its source is
catenary when its target is catenary. -/
#check (AlgebraicGeometry.Scheme.catenarySpace_of_isImmersion :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [CatenarySpace Y], CatenarySpace X)
