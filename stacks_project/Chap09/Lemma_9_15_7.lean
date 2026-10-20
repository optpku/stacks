/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Normal.Embeddings
import StacksCheckRecall

@[expose] public section

/- Lemma 9.15.7 (Tag 0BME): every `K`-algebra map into a normal extension has an extension in
`Gal(L/K)`. -/
@[stacks 0BME]
#check FieldExtension.galExtensionOfAlgHom
#check FieldExtension.galExtensionOfAlgHom_comp
#check FieldExtension.existsGalExtendingAlgHom
