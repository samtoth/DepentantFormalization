module Cat.Bi.Instances.Slice where

open import Cat.Prelude
open import Cat.Bi.Base
import Cat.Reasoning as CR     

module _ {o ℓ ℓ'} (𝓒 : Prebicategory o ℓ ℓ') where
  private
    module C = Prebicategory 𝓒
    variable a b c : C.Ob
    

  record /-Obj (c : C.Ob) : Type (o ⊔ ℓ) where
    constructor cut
    field
      {domain} : C.Ob
      map      :  domain C.↦ c
    
  -- record /-Hom (a b : /-Obj c) : Type (ℓ ⊔ ℓ') where
  --   no-eta-equality
  --   private
  --     module a = /-Obj a
  --     module b = /-Obj b
  --   field
  --     map      : a.domain C.↦ b.domain
  --     commutes : CR._≅_ (C.Hom a.domain c) a.map (b.map C.⊗ map)

  /-Hom : (a b : /-Obj c) → Precategory ℓ ℓ'
  /-Hom a b = cat
    where module a = /-Obj a
          module b = /-Obj b 
          cat : Precategory ℓ ℓ'
          cat = C.Hom a.domain b.domain

  _//_ : C.Ob → Prebicategory (o ⊔ ℓ) ℓ ℓ'
  _//_ c = prebicat
    where prebicat : Prebicategory _ _ _
          prebicat .Prebicategory.Ob = /-Obj c
          prebicat .Prebicategory.Hom = /-Hom
          prebicat .Prebicategory.id = C.id
          prebicat .Prebicategory.compose = {! C.compose  !}
          prebicat .Prebicategory.unitor-l = {!   !}
          prebicat .Prebicategory.unitor-r = {!   !}
          prebicat .Prebicategory.associator = {!   !}
          prebicat .Prebicategory.triangle = {!   !}
          prebicat .Prebicategory.pentagon = {!   !}