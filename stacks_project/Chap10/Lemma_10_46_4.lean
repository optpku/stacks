/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.PowerImage.Spectrum
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.4

@stack 0EUH

The square/cube generation criterion is owned by `RingHom.PowerImage.SquareCube`.  The
source-labelled entry below recalls the fine-grained reusable conclusions, including the
bundled `IsSubintegral` result and its residue-field criterion.
-/

/- Lemma 10.46.4 (1): square/cube generation induces isomorphisms on residue fields. -/
@[stacks 0EUH "(1), residue-field isomorphisms"]
#check @RingHom.PowerImage.SquareCube.mapsBijective

/- Lemma 10.46.4 (2): with locally nilpotent kernel, contraction is a homeomorphism. -/
@[stacks 0EUH "(2), homeomorphism on spectra"]
#check @RingHom.PowerImage.SquareCube.isHomeomorph_comap

/- Lemma 10.46.4: the two conclusions are bundled by the canonical subintegral predicate. -/
@[stacks 0EUH "subintegral package"]
#check @RingHom.PowerImage.SquareCube.isSubintegral

/- Lemma 10.46.4 (3): square/cube generation and the locally nilpotent kernel persist after base
change. -/
@[stacks 0EUH "(3), square/cube generation after base change"]
#check @RingHom.PowerImage.SquareCube.BaseChange.isGenerated

@[stacks 0EUH "(3), locally nilpotent kernel after base change"]
#check @RingHom.PowerImage.SquareCube.BaseChange.ker_isLocallyNilpotent

#check @RingHom.PowerImage.SquareCube.BaseChange.isSubintegral
