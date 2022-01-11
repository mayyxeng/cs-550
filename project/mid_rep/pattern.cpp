

class Mother {
public:
    enum class Types {
        TMyConcreteClass,
        TMyConcreteClass2,
        C3
    };
    virtual Types getType() const = 0;

};

class MyConcreteClass: public Mother {
    virtual Types getType() const { return Types::TMyConcreteClass; }
};

class MyConcreteClass2: public Mother {
    virtual Types getType() const { return Types::TMyConcreteClass2; }
};


Mother* p;

// template<typename Ret, typename Fn>
// Ret matcher(Fn&& matfn, )
switch(p->getType()) {

    case Types::TMyConcreteClass:
        dynamic_cast<MyConcreteClass>(p)

    break;

}