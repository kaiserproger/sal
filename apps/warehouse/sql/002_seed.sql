BEGIN;

INSERT INTO warehouses (id, name, available) VALUES
    (1, 'Central warehouse', true),
    (2, 'Outlet warehouse', true),
    (3, 'Closed warehouse', false)
ON CONFLICT DO NOTHING;

INSERT INTO items (id, name, size, code) VALUES
    (1, 'Red shirt', 'M', 'SKU-RED-M'),
    (2, 'Blue "wind" jacket', 'L', 'SKU-BLUE-L'),
    (3, 'Black shoes', '42', 'SKU-ZERO-42'),
    (4, 'Куртка', 'M', 'SKU-ЁЖ-М')
ON CONFLICT DO NOTHING;

-- Rerunning seeds never overwrites quantities or existing reservations.
INSERT INTO inventory (warehouse_id, item_id, quantity) VALUES
    (1, 1, 10),
    (1, 2, 5),
    (1, 3, 0),
    (1, 4, 7),
    (2, 1, 3),
    (2, 2, 2),
    (3, 1, 4)
ON CONFLICT DO NOTHING;

SELECT setval(pg_get_serial_sequence('warehouses', 'id'), (SELECT max(id) FROM warehouses));
SELECT setval(pg_get_serial_sequence('items', 'id'), (SELECT max(id) FROM items));

COMMIT;
