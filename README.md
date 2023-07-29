# IMP_DP
命令式动态规划类算法程序推导及机械化验证

本文给出了命令式动态规划类算法程序推导以及机械验证框架,实例化了0-1背包问题（KS）和最长公共子序列（LCS）的推导和验证.

ks.thy是对KS验证脚本;lcs.thy是对LCS验证脚本.

该验证依赖于%ISABELLE_HOME%\src\HOL\Hoare文件夹，Arith2.thy和Hoare_Logic.thy是主要依赖脚本代码.

本文基于S.Wimmer实现的动态规划类算法Isabelle/HOL函数式建模与验证,主要实现代码可参考https://www.isa-afp.org/entries/Monad_Memo_DP.html.
其中Knapsack.thy和Longest_Common_Subsequence.thy分别是KS和LCS函数式验证脚本
