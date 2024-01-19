import java.math.BigInteger;
import java.util.*;

import it.unisa.dia.gas.jpbc.Element;
import it.unisa.dia.gas.jpbc.Field;
import it.unisa.dia.gas.jpbc.Pairing;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;

public class CPA {
    // 属性集合
    static List<String> U = Arrays.asList("man", "smart", "handsome", "ugly", "stupid");
    // 属性集合的编码
    static List<BigInteger> U_bm = new ArrayList<>();
    // 属性个数
    static BigInteger l = BigInteger.valueOf(U.size());
    // 默认属性集合
    static List<String> U2 = Arrays.asList("human", "eat", "sleep", "drink");
    // 默认属性的编码
    static List<BigInteger> U2_bm = new ArrayList<>();
    // 属性顺序编码，记录下一个编码的属性id
    static BigInteger bmid = BigInteger.valueOf(1);
    // 属性编码映射，只有setup阶段会对属性进行编码，后续使用的属性集合都是setup编码集合的子集，要获取这些集合的编码就需要在setup阶段保存映射
    static Map<String, BigInteger> att2id = new HashMap<>();
    // 公共参数params(g,g2,Z,h0,h1,...,h2l-1)
    static List<Element> params = new ArrayList<>();
    static List<Element> h = new ArrayList<>();

    // 门限访问结构
    public static class MX {
        List<String> S;
        List<BigInteger> S_bm;
        BigInteger t;
    }

    // 密文结构
    public static class CT {
        Element C0, C1, C2;
    }

    // 双线性映射 G1 × G1 → GT
    // 从文件导入椭圆曲线参数
    static Pairing bp = PairingFactory.getPairing("a.properties");
    // 生成两个群
    static Field G1 = bp.getG1();
    static Field GT = bp.getGT();
    static Field Zr = bp.getZr(); // 整数域
    BigInteger p = G1.getOrder();// 阶


    public static void main(String[] args) {
        Element msk = Setup("11", U);
        List<String> A = Arrays.asList("man", "smart", "handsome");
        List<List<Element>> sk = keyGen(msk.toBigInteger(), A);
        MX mx = new MX();
        mx.S = Arrays.asList("man", "smart", "handsome", "ugly");
        mx.S_bm = getMyEncode(mx.S);
        mx.t = BigInteger.valueOf(3);
        Element M = GT.newRandomElement().getImmutable();
        System.out.println(M);
        CT encrypt = Encrypt(M, mx);
        Element decrypt = Decrypt(mx, sk, A, encrypt);
        System.out.println(decrypt);
    }

    /**
     * Setup
     *
     * @param lambda 安全参数
     * @param U      属性集合
     * @return 主密钥msk，公共参数params(g,g2,Z,h0,h1,...,h2l-1)
     */
    public static Element Setup(String lambda, List<String> U) {
        Element g = G1.newRandomElement().getImmutable(); // 生成元
        //  1 中央属性机构选择编码函数ρ，将l个属性中的每一个属性atti编码为不同的元素 ρ(atti) = xi ∈ Zp，简单来说就是定义 ρ(atti) = i 对每一个atti ∈ U
        U_bm = myEncode(U);
        //  2 除了U中的l个属性外，属性机构还需要选取 l - 1 个默认属性U’ = {att’1,att’2,…,att’l-1} = {l+1,…,2l - 1}。系统中的每个用户都拥有默认属性U’(|U’| = l - 1)。
        U2_bm = myEncode(U2);
        //  3 中央属性机构从G中随即均匀的选择 g2,h0,h1,…,h2l-1, 选择随机数 x ∈ Zp
        Element g2 = G1.newRandomElement().getImmutable();
        for (int i = 0; i < 2 * l.intValue(); i++) {
            h.add(G1.newRandomElement().getImmutable());
        }
        Element x = Zr.newRandomElement().getImmutable();
        // 4 计算 g1 = g^x，Z = e(g1,g2)
        Element g1 = g.powZn(x);
        Element Z = bp.pairing(g1, g2);
        // 5 主密钥msk = x，公共参数params = (g,g2,Z,h0,h1,…,h2l-1)
        Element msk = x;
        params.add(g);
        params.add(g2);
        params.add(Z);
        params.addAll(h);
        return msk;
    }

    /**
     * @param msk 主密钥
     * @param A   用户属性集合
     * @return 用户私钥{ski}
     */
    static List<List<Element>> keyGen(BigInteger msk, List<String> A) {
        // 1 随机选取l-1次多项式q(·)，其中q(0) = x
        List<BigInteger> poly = generatePolynomial(l.intValue() - 1, msk);
        // 2 对每一个属性 i ∈ (A ∪ U’)，属性机构从Zp中选取随机数ri，计算  ski =(g2q(i)(h0hi)ri , gri , h1ri , ... , hi−1ri , hi+1ri , ... , h2l-1ri)    =(ai , bi , ci,1 , ... , ci,i−1 , ci,i+1 , ... , ci,2l−1);
        List<BigInteger> A_bm = getMyEncode(A);
        List<BigInteger> AUnionU2 = union(A_bm, U2_bm);
        List<List<Element>> sk = new ArrayList<>();
        for (int i = 0; i < bmid.intValue(); i++) {
            sk.add(new ArrayList<>());
        }
        Element g = params.get(0);
        Element g2 = params.get(1);
        for (BigInteger i : AUnionU2) {
            Element ri = Zr.newRandomElement().getImmutable();
            Element ai = (g2.pow(polynomial(poly, i))).mul((h.get(0).mul(h.get(i.intValue()))).powZn(ri));
            sk.get(i.intValue()).add(ai);
            sk.get(i.intValue()).add(g.mulZn(ri));
            for (int j = 1; j < 2 * l.intValue(); j++) {
                if (j == i.intValue()) {
                    continue;
                }
                sk.get(i.intValue()).add(h.get(j).powZn(ri));
            }
        }
        return sk;
    }

    /**
     * @param sk 属性集A的私钥
     * @param A2 属性集A的子集
     * @return 属性集A2的私钥
     */
    List<List<Element>> delegate(List<List<Element>> sk, List<String> A2) {
        Element g = params.get(0);
        List<BigInteger> A2_bm = getMyEncode(A2);
        List<BigInteger> A2UnionU2 = union(A2_bm, U2_bm);
        List<List<Element>> sk2 = new ArrayList<>(bmid.intValue());
        for (BigInteger i : A2UnionU2) {
            Element ri = Zr.newRandomElement().getImmutable();
            sk2.get(i.intValue()).add(sk.get(i.intValue()).get(0).mul(h.get(0).mul(h.get(i.intValue())).powZn(ri)));
            sk2.get(i.intValue()).add(sk.get(i.intValue()).get(1).mul(g.powZn(ri)));
            for (int j = 1; j <= 2 * l.intValue() - 1; j++) {
                if (j == i.intValue()) {
                    continue;
                }
                sk2.get(i.intValue()).add(sk.get(i.intValue()).get(j + 1).mul(h.get(j).powZn(ri)));
            }
        }
        return sk2;
    }

    /**
     * @param M 待加密消息
     * @param Y 门限访问结构
     * @return 返回加密后的密文
     */
    static CT Encrypt(Element M, MX Y) {
        // 1 发送者从默认属性集U’中挑选前l-t个元素Ω = {l+1,l+2,…,2l-t}
        List<BigInteger> O = U2_bm.subList(0, l.subtract(Y.t).intValue());
        // 2 发送者选择一个随机数s∈Zp，计算密文CT = (C0,C1,C2)
        Element g = params.get(0);
        Element s = Zr.newRandomElement().getImmutable();
        Element C0 = M.mul(params.get(2).powZn(s));
        Element C1 = g.powZn(s);
        List<BigInteger> SUnionO = union(O, Y.S_bm);
        Element C2 = h.get(0);
        for (BigInteger j : SUnionO) {
            C2 = C2.mul(h.get(j.intValue()));
        }
        C2 = C2.powZn(s);
        CT ct = new CT();
        ct.C0 = C0;
        ct.C1 = C1;
        ct.C2 = C2;
        return ct;
    }

    /**
     * @param Y  门限访问结构
     * @param sk 用户私钥
     * @param A  满足门限结构的用户属性子集
     * @param ct 密文
     * @return 明文
     */
    static Element Decrypt(MX Y, List<List<Element>> sk, List<String> A, CT ct) {
        // 1.用户从默认属性集U’中挑选前l-t个元素Ω = {l+1,l+2,…,2l-t}
        List<BigInteger> O = U2_bm.subList(0, l.subtract(Y.t).intValue());
        List<BigInteger> A_bm = getMyEncode(A);
        List<BigInteger> AunionO = union(A_bm, O);
        List<BigInteger> SunionO = union(Y.S_bm, O);
        // 2
        Element D1 = G1.newOneElement().getImmutable();
        for (BigInteger i : AunionO) {
            Element t = sk.get(i.intValue()).get(0);
            for (BigInteger j : SunionO) {
                if (i.equals(j)) {
                    continue;
                }
                t = t.mul(sk.get(i.intValue()).get(j.intValue() + 1));
            }
            int up = 1;
            int down = 1;
            for (BigInteger j : AunionO) {
                if (i.equals(j)) {
                    continue;
                }

                up *= -j.intValue();
                down *= (i.intValue() - j.intValue());
            }
            // TODO：up/down 除不尽
            t = t.pow(BigInteger.valueOf((up / down)));
            D1 = D1.mul(t);
        }
        Element D2 = G1.newOneElement().getImmutable();
        for (BigInteger i : AunionO) {
            Element t = sk.get(i.intValue()).get(1);
            int up = 1;
            int down = 1;
            for (BigInteger j : AunionO) {
                if (i.equals(j)) {
                    continue;
                }
                up *= -j.intValue();
                down *= (i.intValue() - j.intValue());
            }
            t = t.pow(BigInteger.valueOf((up / down)));
            D2 = D2.mul(t);
        }
        // 3
        Element c0 = ct.C0;
        Element c1 = ct.C1;
        Element c2 = ct.C2;
        Element M = c0.mul(bp.pairing(c2, D2)).div(bp.pairing(c1, D1));
        return M;
    }

    /**
     * 对属性编码
     *
     * @param U 编码属性集合
     * @return 编码后的集合
     */
    static List<BigInteger> myEncode(List<String> U) {
        List<BigInteger> ret = new ArrayList<>();
        for (String s : U) {
            att2id.put(s, bmid);
            ret.add(bmid);
            bmid = bmid.add(BigInteger.valueOf(1));
        }
        return ret;
    }

    /**
     * 获取属性的编码
     *
     * @param A 属性集合
     * @return 属性集合的编码
     */
    static List<BigInteger> getMyEncode(List<String> A) {
        List<BigInteger> ret = new ArrayList<>();
        for (String s : A) {
            ret.add(att2id.get(s));
        }
        return ret;
    }

    /**
     * 随机生成多项式
     *
     * @param degree 多项式次数
     * @param msk    主密钥
     * @return 生成的多项式，用数组表示,下标为次数，元素为系数
     * （例：[x,0,-1,2,3] 表示 x-1*a^2+2*a^3+3*a^4）
     */
    static List<BigInteger> generatePolynomial(int degree, BigInteger msk) {
        List<BigInteger> poly = new ArrayList<>();
        poly.add(msk);
        for (int i = 1; i <= degree; i++) {
            poly.add(Zr.newRandomElement().getImmutable().toBigInteger());
        }
        return poly;
    }

    /**
     * 计算多项式的值
     *
     * @param poly generatePolynomial方法生成的多项式
     * @param x    多项式中变量的取值
     * @return 多项式计算结果
     */
    static BigInteger polynomial(List<BigInteger> poly, BigInteger x) {
        BigInteger tmp = BigInteger.valueOf(1);
        BigInteger ret = BigInteger.valueOf(0);
        for (BigInteger i : poly) {
            ret = ret.add(tmp.multiply(i));
            tmp = tmp.multiply(x);
        }
        return ret;
    }

    /**
     * 求两个int集合的并集
     */
    static List<BigInteger> union(List<BigInteger> a, List<BigInteger> b) {
        Map<BigInteger, Boolean> set = new HashMap<>();
        for (BigInteger i : a) {
            set.put(i, true);
        }
        for (BigInteger i : b) {
            set.put(i, true);
        }
        return new ArrayList<>(set.keySet());
    }
}