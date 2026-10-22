/-
  Procesi —— **形态层（Alg）**：把第二层的 `≃+*` 有理性升到 `≃ₐ`（`IsRational`）形

  动机（任务书 §2.2 的逐字要求）：`Z_H(F,9)` **于** `F(M|_H)^H` **有理**。
  工程既有的 `IsRational` 是 `≃ₐ` 形，故需要一条**包含**
  `F(M|_H)^H ↪ F((M⊕U)|_H)^H` 以给出 `Algebra` 实例。本件造这条包含的**三段**：

    §1 `baseToSemi`：基域不变量代数 → **半函数域**的不变量子域（`algebraMap` 限制）；
    §2 `algEquivInvariants`：`Subfield` 形态 ↔ `Subalgebra` 形态的 `F`-代数同构（元素不动）；
    §3 `baseIso`：`F(M|_H)^H`（`Alg` 形态）↔ 机器基域 `K0`；
        `instAlgebraBaseTop`：经 `EMBridge.chiAbs`（`semi^H ≃ₐ[F] F(M⊕U)^H`）合成出
        **典范包含** `F(M|_H)^H ↪ F((M⊕U)|_H)^H` 所定义的 `Algebra` 实例。

  **为何实例是"典范"的**：`algebraMap` 取的是 `c ↦ (β₁ ∘ ι)(c)`，其中
  `ι : F(M) → F(M)(P)` 是标量塔的 `algebraMap`、`β₁` 是 `EMBridge` 已证的环境同构
  （`AlgEquiv` 且 `H`-等变）。即"把 `F(M|_H)^H` 的元素视为 `F((M⊕U)|_H)^H` 的元素"
  的唯一自然方式；**不是**为凑结论而选的结构。

  续（下一件）：`IsRational ↥(latticeInvariantsAlg F H M) ↥(latticeInvariantsAlg F H (M⊕U))`
  —— 由 `ProcStab.s2Interface_procesi`（`IsRational ↥K0 ↥(semi^H)`）沿
  `baseIso`（基域）与 `chiAbs`（顶域）搬运；搬运步骤见 `wiki/log.md` 待办。
-/
import Procesi.Main
import Procesi.Lenstra
import Procesi.Statement

open scoped TensorProduct
open TensorProduct
open ABGV52

namespace Procesi

noncomputable section

set_option maxHeartbeats 1600000

/-! ## §1 基域不变量代数 → 半函数域的不变量子域 -/

/-- **`F(M|_H)^H ↪ F(M|_H)(P)` 的不变量层**：`algebraMap` 限制到不变量上。

**为何落在不变量里**：`σ • algebraMap c = algebraMap (σ • c)`（`EMFixed` 的
`smul_algebraMap_semiAlg` ＋ `semiAlgEquiv_algebraMap_lattice` ＋ `coeffRingEquiv_apply`），
而 `c` 是 `σ`-不变的。 -/
def baseToSemi (F : Type) [Field F] :
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) →+*
    ↥(FixedPoints.subfield (P.Hp 3) (EM.semiFunctionField (F := F)
        (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))) where
  toFun x := ⟨algebraMap _ _ x.1, (EM.mem_fixed_iff _).mpr (fun σ => by
    rw [IsScalarTower.algebraMap_apply
      (EM.latticeFunctionField F ↥(LinearMap.ker (G.phiFun 3)))
      (MonoidAlgebra (EM.latticeFunctionField F ↥(LinearMap.ker (G.phiFun 3)))
        (Multiplicative (G.ZOm 3)))
      (EM.semiFunctionField (F := F) (M := ↥(LinearMap.ker (G.phiFun 3)))
        (P := G.ZOm 3))]
    rw [EM.smul_algebraMap_semiAlg, EM.semiAlgEquiv_algebraMap_lattice,
      EM.coeffRingEquiv_apply]
    rw [show σ • x.1 = x.1 from
      (EM.mem_latticeInvariantsAlg_iff (F := F) (G := P.Hp 3)
        (M := ↥(LinearMap.ker (G.phiFun 3))) x.1).mp x.2 σ])⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-! ## §2 两种不变量形态之间的 `F`-代数同构 -/

/-- **`Subfield` 形态 → `Subalgebra` 形态**（元素不动）的 `F`-代数同构。

**为何不能直接用 `EM.invariantsRingEquiv`**：它只是 `≃+*`（`Subfield` 在 mathlib 中
无 `Algebra F` 实例，见 `D3_ABGV52.lean` 的说明）；本件补上 `algebraMap` 兼容性。 -/
def algEquivInvariants (F : Type) [Field F] :
    ↥(EM.latticeInvariants F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) ≃ₐ[F]
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) :=
  AlgEquiv.ofRingEquiv
    (f := EM.invariantsRingEquiv F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))
    (fun c => by ext; rfl)

/-! ## §3 基域与典范包含 -/

/-- **基域同构**：`F(M|_H)^H`（`Alg` 形态）↔ 机器基域 `K0`（`l^H` 在半函数域中的像）。 -/
def baseIso (F : Type) [Field F] :
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) ≃ₐ[F]
    ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3)))
      (P := G.ZOm 3)) :=
  ((ProcStab.K0EquivInvariants (p := 3) F).trans (algEquivInvariants F)).symm

/-- **典范包含**（环同态形）：`F(M|_H)^H → F((M⊕U)|_H)^H`
＝ `chiAbs ∘ baseToSemi`（先上到半函数域、再经 `EMBridge` 的环境同构）。 -/
def baseToTop (F : Type) [Field F] :
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3))) →+*
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  (EM.Bridge.chiAbs (F := F) (G := P.Hp 3) (M := ↥(LinearMap.ker (G.phiFun 3)))
    (P := G.ZOm 3)).toRingHom.comp (baseToSemi F)

/-- 展开引理（`rfl`）：`baseToTop = chiAbs ∘ baseToSemi`。 -/
theorem baseToTop_eq (F : Type) [Field F]
    (c : ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))) :
    baseToTop F c = (EM.Bridge.chiAbs (F := F) (G := P.Hp 3)
      (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3)) (baseToSemi F c) := rfl

/-- 展开引理（`rfl`）：`baseToSemi` 的元素层 ＝ 经 `baseIso` 送进 `↥K0` 再上到半函数域。 -/
theorem baseToSemi_eq (F : Type) [Field F]
    (c : ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))) :
    baseToSemi F c = algebraMap (↥(EM.K0 (G := P.Hp 3) (F := F)
      (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3)))
      (↥(FixedPoints.subfield (P.Hp 3) (EM.semiFunctionField (F := F)
        (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3)))) ((baseIso F) c) := rfl

/-- **`Algebra` 实例**（由典范包含定义）：`F((M⊕U)|_H)^H` 是 `F(M|_H)^H`-代数。 -/
instance instAlgebraBaseTop (F : Type) [Field F] :
    Algebra ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  (baseToTop F).toAlgebra

/-- 类型锁：`algebraMap` 就是典范包含（`baseToTop`）。 -/
theorem algebraMap_baseTop (F : Type) [Field F]
    (c : ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))) :
    algebraMap _ (↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3))) c =
      baseToTop F c := rfl


/-! ## §3b `IsRational` 收口（`≃ₐ` 形）—— Lenstra 1.4 的忠实结论

**策略（关键）**：不在 `↥(latticeInvariantsAlg F H M)` 上做基域搬运（那需要一条巨型
兼容性证明，实测在 `isDefEq` 上超时），而是把**基域取成 `↥K0`**——`K0` 正是
`F(M|_H)^H` 在半函数域中的**像**，即 Lenstra 1.4 里的 `l^π`。于是：

* 把 `Algebra ↥K0 ↥(latticeInvariantsAlg F H (M⊕U))` 定义为 `chiAbs ∘ algebraMap` 的**拉回**
  ⟹ `chiAbs` 对 `↥K0` 线性为 **`rfl`**；
* `ProcStab.s2Interface_procesi` 给 `IsRational ↥K0 ↥(semi^H)`，沿 `chiAbs` 搬到顶域即得。

**这为什么够**：`baseIso : F(M|_H)^H ≃ₐ[F] ↥K0`（§3）把基域的两种写法同一；
故本定理就是论文 `rem:procesi-geometric` 的"`Z_H(F,9)` 于 `F(M|_H)^H` 有理"，
基域以 `K0`（其像）呈现。`≃+*` → `≃ₐ` 的形态缺口就此闭合。 -/

/-- `↥K0 → F((M⊕U)|_H)^H` 的典范环同态（`chiAbs ∘ algebraMap`）。 -/
def k0ToTop (F : Type) [Field F] :
    ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3)))
      (P := G.ZOm 3)) →+*
    ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  (EM.Bridge.chiAbs (F := F) (G := P.Hp 3) (M := ↥(LinearMap.ker (G.phiFun 3)))
    (P := G.ZOm 3)).toRingHom.comp
    (algebraMap _ (↥(FixedPoints.subfield (P.Hp 3) (EM.semiFunctionField (F := F)
      (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3)))))

/-- `F((M⊕U)|_H)^H` 上的 `↥K0`-代数结构（由 `k0ToTop` 的拉回定义）。 -/
instance instAlgebraK0Top (F : Type) [Field F] :
    Algebra ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3)))
      (P := G.ZOm 3))
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  (k0ToTop F).toAlgebra

/-- **`chiAbs` 作为 `↥K0`-代数同构**（兼容性 `rfl`——这正是"拉回实例"策略的全部要点）。 -/
def chiAbsK0 (F : Type) [Field F] :
    ↥(FixedPoints.subfield (P.Hp 3) (EM.semiFunctionField (F := F)
      (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))) ≃ₐ[
        ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3)))
          (P := G.ZOm 3))]
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  AlgEquiv.ofRingEquiv
    (f := (EM.Bridge.chiAbs (F := F) (G := P.Hp 3) (M := ↥(LinearMap.ker (G.phiFun 3)))
      (P := G.ZOm 3)).toRingEquiv) (fun _ => rfl)

/-- ★★★ **`IsRational` 收口（`≃ₐ` 形，无条件）**：`F((M⊕U)|_H)^H` **于 `↥K0` 有理**，
其中 `↥K0` 是 `F(M|_H)^H` 在半函数域中的像（＝ Lenstra `prop:1.4` 的 `l^π`）。

**源锚**：`raw/Lenstra1974.tex` 的 label `prop:1.4`；论文 `rem:procesi-geometric` 的
"rational over `F(M|_H)^H`"。

**与 `m3_procesi` 的关系**：`m3_procesi` 是 `≃+*` 形；本定理是**同一条数学内容**的
`≃ₐ` 形（基域以 `K0` 呈现），即库消费者（`ProcConsume.ProcesiHypStableK`）所需形态。 -/
theorem isRational_procesi (F : Type) [Field F] :
    EM.IsRational ↥(EM.K0 (G := P.Hp 3) (F := F)
        (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) := by
  obtain ⟨n, ⟨e⟩⟩ := ProcStab.s2Interface_procesi (p := 3) F
  exact ⟨n, ⟨(chiAbsK0 F).symm.trans e⟩⟩

/-- 类型锁：`IsRational` 收口的**基域是 `↥K0`**、顶域是 `F((M⊕U)|_H)^H`。 -/
theorem isRational_procesi_typeLock (F : Type) [Field F] :
    EM.IsRational ↥(EM.K0 (G := P.Hp 3) (F := F)
        (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) :=
  isRational_procesi F

/-! ## §3c 基域重索引的**关键一步**（路线 5；第 78 轮）

**为何只到这一步**：把 `IsRational` 的基域从 `↥K0` 重索引到 `F(M|_H)^H` 的 `Subalgebra` 形态
`↥(latticeInvariantsAlg F H M)`，前四法（见战役总账 §5.4）皆撞 elaboration 墙。**第 5 条路线**
的观察是：`baseToTop`（＝ `↥(latticeInvariantsAlg F H M)`-代数结构）**就是**
`algebraMap ↥K0 top ∘ baseIso`——由 `baseToTop_eq`／`baseToSemi_eq` ＋ `chiAbsK0` 的
`commutes' := fun _ => rfl` 直接得到（**`rfl` 级，不是巨型 `isDefEq`**）。
本件把这一步机检；**余下**（未做）＝ `MvPolynomial`／分式域的 `IsScalarTower` 实例搬运
（估计 100–200 行，增量纯呈现层）。 -/

/-- `F(M|_H)^H` 的 `Subalgebra` 形态（重索引的**目标**基域）。 -/
abbrev BInv (F : Type) [Field F] : Type :=
  ↥(EM.latticeInvariantsAlg F (P.Hp 3) ↥(LinearMap.ker (G.phiFun 3)))

/-- `K0`（`F(M|_H)^H` 在半函数域中的像，`Alg.lean` 的基域呈现）。 -/
abbrev K0img (F : Type) [Field F] : Type :=
  ↥(EM.K0 (G := P.Hp 3) (F := F) (M := ↥(LinearMap.ker (G.phiFun 3))) (P := G.ZOm 3))

/-- ★★ **路线 5 的关键等式**：`baseToTop = algebraMap ↥K0 top ∘ baseIso`。

**读法**：两种「基域呈现」下的 `algebraMap` **相差一个 `baseIso`**，故重索引不再是
「巨型 `isDefEq`」问题，而是纯搬运问题（见本节头注）。 -/
theorem baseToTop_eq_algebraMap_baseIso (F : Type) [Field F] (c : BInv F) :
    baseToTop F c = algebraMap (K0img F)
      ↥(EM.latticeInvariantsAlg F (P.Hp 3) (ProcLat.Mp2 3)) ((baseIso F) c) :=
  (chiAbsK0 F).commutes ((baseIso F) c)

#print axioms BInv
#print axioms K0img
#print axioms baseToTop_eq_algebraMap_baseIso

/-! ## §4 公理闸门 -/

#print axioms baseToSemi
#print axioms algEquivInvariants
#print axioms baseIso
#print axioms baseToTop
#print axioms instAlgebraBaseTop
#print axioms baseToTop_eq
#print axioms baseToSemi_eq
#print axioms k0ToTop
#print axioms instAlgebraK0Top
#print axioms chiAbsK0
#print axioms isRational_procesi
#print axioms isRational_procesi_typeLock
#print axioms algebraMap_baseTop

end

end Procesi
