#ifndef KOME_TRANSPORT_HPP
#define KOME_TRANSPORT_HPP

#include "kome.h"
#include <cstdint>
#include <cstddef>
#include <functional>

namespace kome {

/* Internal transport adapter base class */
class KomeTransportAdapter {
public:
    using RecvCallback = std::function<void(const uint8_t *peer_fp,
                                            const uint8_t *data, size_t len)>;
    using PeerCallback = std::function<void(const uint8_t *peer_fp, int connected)>;

    virtual ~KomeTransportAdapter() = default;

    virtual void send(const uint8_t *peer_fp, const uint8_t *data, size_t len) = 0;

    void set_recv_callback(RecvCallback cb) { recv_cb_ = std::move(cb); }
    void set_peer_callback(PeerCallback cb) { peer_cb_ = std::move(cb); }

protected:
    RecvCallback recv_cb_;
    PeerCallback peer_cb_;
};

/* Wraps the public C KomeTransport struct */
class KomeGenericTransport : public KomeTransportAdapter {
public:
    explicit KomeGenericTransport(KomeTransport *t) : transport_(t) {
        /* Wire the C callbacks to forward into our recv_cb_ / peer_cb_ */
        transport_->set_recv_callback(transport_,
            [](void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len) {
                auto *self = static_cast<KomeGenericTransport*>(ud);
                if (self->recv_cb_) self->recv_cb_(peer_fp, data, len);
            }, this);

        transport_->set_peer_callback(transport_,
            [](void *ud, const uint8_t *peer_fp, int connected) {
                auto *self = static_cast<KomeGenericTransport*>(ud);
                if (self->peer_cb_) self->peer_cb_(peer_fp, connected);
            }, this);
    }

    void send(const uint8_t *peer_fp, const uint8_t *data, size_t len) override {
        if (transport_ && transport_->send)
            transport_->send(transport_, peer_fp, data, len);
    }

private:
    KomeTransport *transport_;
};

} /* namespace kome */

#endif /* KOME_TRANSPORT_HPP */
