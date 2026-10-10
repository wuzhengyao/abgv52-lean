/-
  ABGV-5.2 —— Ext LES 塌缩件：探针 2（临时件；主件签名与跨模块导入核对）

  目的：对 `ExtLES_ABGV52.lean` 作两件事——
    ① 跨模块导入可用性（主循环把两件合成时需要 import 该 olean）；
    ② 打印主声明的**精确签名（含宇宙）**，供主循环注册对表。
-/
import ABGV52.ExtLES_ABGV52

open CategoryTheory
open CategoryTheory.Abelian

namespace ABGV52

section

set_option pp.universes true in
#check @instHasExtRepLES

set_option pp.universes true in
#check @regZ_rho_apply_eq

set_option pp.universes true in
#check @regZIsoLeftRegular

set_option pp.universes true in
#check @instProjectiveRegZ

set_option pp.universes true in
#check @extConnectingMap

set_option pp.universes true in
#check @extConnectingMap_injective

set_option pp.universes true in
#check @extConnectingMap_surjective

set_option pp.universes true in
#check @extOneIH_addEquiv_extTwoTriv

end

-- 用户层复合检验：主定理可直接使用（导入路径下的实例/宇宙自洽）
-- （2026-10-10 注册收口：由匿名 `example` 升为具名定理并挂公理门——checker 的 [2b]
-- 反空转规则要求注册件 `#print axioms` 非空，内容不变。）
theorem probeLES2_composite_available (L : Rep ℤ H) :
    Nonempty (Ext I_H_rep L 1 ≃+ Ext trivRep L 2) :=
  ⟨extOneIH_addEquiv_extTwoTriv L⟩

#print axioms probeLES2_composite_available

end ABGV52
